/*
Author: COKPOWEHEU
License: MIT
Description (UTF-8)

Компилировалось в Debian с помощью gcc-4.9.2 командой
$gcc -o prog -Wall -Os approx.c
$i686-w64-mingw32-gcc-4.9-win32 -o prog.exe -Wall -Os approx.c

Теоретически должно заработать и при компиляции чем-нибудь другим, но, возможно, придется поплясать с бубном.

Программа нахождения максимально близкого заданному набору точек полинома заданной степени методом наименьших квадратов
Если разобраться с этим методом для полинома станет ясно что частные производные суммы квадратов по отдельным переменным
представляют систему линейных уравнений из dim уравнений и dim неизвестных, где dim - максимальная степерь полинома.
Такая система идеально записывается в виде матрицы (dim+1)x(dim) решить которую - дело техники (см описание Calc())
каждый элемент представляет собой сумму неких функций отдельных точек (о самой функции чуть дальше) поэтому обрабатываются они независимо друг от друга
просто складываясь в матрице. Функция преобразования координат отдельной точки в слагаемое для матрицы: для коэффициентов это всего лишь
dk = x^(i+j), где i и j - координаты в матрице. Для столбца результатов не намного сложнее: dr = y*x^j где j - номер строки.
Сначала матрица заполняется нулями, потом в нее по одной добавляются интересующие нас точки, потом рассчитываются значения коэффициентов.
Рассчитывать можно несколькими способами, самый очевидный - метод Гаусса, через определители. Но такой лобовой рассчет неизбежно будет
содержать рекурсию, что здорово замедлит программу и снизит ее надежность, поэтому был применен другой метод - приведение к диагональному виду. К сожалению, более простых способов (учитывающих равенство элементов с равными суммами индексов m[i,j], где i+j=const) найти
не удалось
Подробнее о математической модели внизу файла, в формате LaTeX
*/

const unsigned int version_1	=	1;
const unsigned int version_2	=	0;

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>

//константы ошибок и предупреждений
const int ERR_OK=0;

const int ERR_SUM_LARGE=-1; //переполнение при сложении
const int ERR_MULT_LARGE=-2; //переполнение при умножении
const int ERR_NOT_SPACE=-3; //не хватает ОЗУ для размещения всех массивов
const int ERR_PROG_NOT_MAT=-4; //внутренняя ошибка - использование матрицы до ее инициализации
const int ERR_NOT_IFILE=-5; //входной фацл не найден
const int ERR_PROG_FOUT=-6; //внутренняя ошибка - выходной файл куда-то делся во время выполнения программы, либо был случайно закрыт

const int W_NOT_OFILE=2; //невозможно создать/перезаписать выходной файл
const int W_UNDEF_FLAG=3; //флаг командной строки неопознан
const int W_WRONG_ATTR_M=4; //неправильный атрибут правильного флага (например, символ вместо числа)
const int W_NOTNUM=5; //в одной из входных строк вместо числа обнаружился текст (эта строка будет просто проигнорирована)
const int W_RES_NOT_UNIQ=6; //результат невозможно посчитать однозначно (одно из возможных решений все равно будет выдано)

//символы разделители чисел в строке (пробел, табуляция и перевод строки)
const char splitchars[]=" \t\n";

//битовые флаги для простых настроек
//первые 4 - форматы вывода
#define FLAG_NONE	(0b00<<0) //не выводить результат (хз зачем может понадобиться)			
#define FLAG_POLY	(0b01<<0) //результат в человеко-читаемом виде y = A*x^2 + B*x + C
#define FLAG_LVAL	(0b10<<0) //вывод только коэффициентов, начиная с наименьшей степени (X^0)
#define FLAG_HVAL	(0b11<<0) //вывод только коэффициентов, начиная с наибольшей степени (X^inf)
#define FLAG_MASK_VAL	(0b11<<0) //маска для проверки формата вывода

#define FLAG_EXIT	(1<<2) //флаг выхода, показывает, что считать ничего не надо
#define FLAG_ECHO	(1<<3) //более подробный вывод. Показывает считанные данные и ошибки в них
#define FLAG_EXP	(1<<4) //вывод в экспоненциальной форме
#define FLAG_TEST	(1<<5) //вычисление близости аппроксимации
#define FLAG_OLINE	(1<<6) //вывод в одну строку, а не столбцом


double *mat=NULL;	//рабочая матрица
unsigned int dim=0;	//максимальная степень
int lasterr=0;		//код последней ошибки
unsigned char flag=0;	//флаги
char dec_symb='.';	//десятичный разделитель (по умолчанию - точка
unsigned char exp_len=5;//число знаков в числе
int xpos=0,ypos=1,fskip=0;//столбец иксов и столбец игреков
double xmin=-HUGE_VAL,xmax=HUGE_VAL,ymin=-HUGE_VAL,ymax=HUGE_VAL; //границы, данные вне которых отбрасываются
unsigned int linenum=0; //номер считываемой строки (для указания ошибок и т.п.)
extern char *optarg;	//для использования getpot() и получения нормального списка аргументов
/*
 *  Переопределение стандартных математических операций
 *    Для полиномов высоких степеней подобные ошибки не так уж сложно получить
 */
//сложение
double add(double x,double y){
  if(lasterr<0)return 0;
  x+=y;
  if(errno==ERANGE || x==HUGE_VAL || x==-HUGE_VAL){lasterr=ERR_SUM_LARGE; fprintf(stderr,"Error #%i: coordinates are too large or too small\n",-lasterr);}
  return x;
}
//опять сложение, на этот раз первый операн изменяется
double inc(double *x,double y){
  if(lasterr<0)return 0;
  (*x)+=y;
  if(errno==ERANGE || *x==HUGE_VAL || *x==-HUGE_VAL){lasterr=ERR_SUM_LARGE; fprintf(stderr,"Error #%i: coordinates are too large or too small\n",-lasterr);}
  return *x;
}
//умножение
double mult(double x,double y){
  if(lasterr<0)return 0;
  x*=y;
  if(errno == ERANGE || x==HUGE_VAL || x==-HUGE_VAL){lasterr=ERR_MULT_LARGE; fprintf(stderr,"Error #%i: coordinates are too large or too small\n",-lasterr);}
  return x;
}
/*
 * Функции для работы с матрицей
 *   Учитывая, что Си не позволяет создавать многомерные массивы, работа с ними идет вручную, точнее через макрос MAT
 */
//макрос, отображающий двумерную матрицу на одномерный массив
#define MAT(x,y)	mat[(x)+(y)+(dim)*(y)]

//Очистка матрицы перед использованием. Мало ли что там в ОЗУ было
int clearmatrix(){
  unsigned int i;
  if(mat==NULL||dim==0){ //проверка, инициализирована ли матрица
    lasterr=ERR_PROG_NOT_MAT;
    fprintf(stderr,"Internal error #%i: Programmer, create matrix before using it in [clearmatrix]!\n",-lasterr);
    return lasterr;
  }
  for(i=0;i<dim;i++){MAT(i,0)=0; MAT(dim-1,i)=0; MAT(dim,i)=0;}
  return 0;
}

//добавление очередной точки к матрице. Обновляется не вся матрица, а только первая строка и два последних столбца
//  остальное будет заполнено в специальной функции
int appendmatrix(double x,double y){
  unsigned int i;
  double xn=1; //x^n. Так как каждый элемент матрицы - сумма x^(i+j), значение текущего элемента в нужной степени сохраняем в специальной переменной.
  if(lasterr<0)return lasterr;
  if(mat==NULL||dim==0){
    lasterr=ERR_PROG_NOT_MAT;
    fprintf(stderr,"Internal error #%i: Programmer, create matrix before using it in [appendmatrix]!\n",-lasterr);
    return lasterr;
  }
  //поскольку элементы с равными суммами координат одинаковы, вычисляем только то, что расположено на периметре (mat[i,0], mat[dim,i])
  //остальное заполним просто копированием. Это быстрее, чем вычислять для каждого элемента степень.
  for(i=0;i<dim;i++){
    inc( &MAT(i,0) , xn );
    inc( &MAT(dim,i) , mult(y,xn) );
    xn=mult(xn,x);
  }
  for(i=1;i<dim;i++){
    inc( &MAT(dim-1,i) , xn );
    xn=mult(xn,x);
  }
  return lasterr;
}

//учитывая симметрию матрицы, вычислять все элементы нет необходимости, они заполняются копированием
int fillmat(){
  unsigned int i,j,pos2=0,pos;
  double src,src2;
  if(lasterr<0)return lasterr;
  if(mat==NULL||dim==0){
    lasterr=ERR_PROG_NOT_MAT;
    fprintf(stderr,"Internal error #%i: Programmer, create matrix before using it in [fillmat]!\n",-lasterr);
    return lasterr;
  }
  for(i=1;i<dim;i++){
    pos=i;
    src=mat[pos];
    pos2=dim*(dim-i+1)-i-2;
    src2=mat[pos2];
    for(j=0;j<i;j++){
      pos+=dim;
      mat[pos]=src;
      pos2+=dim;
      mat[pos2]=src2;
    }
  }
  return lasterr;
}

//решение системы линейных уравнений приведением заполненной матрицы к диагональному виду
int calc(){
  if(lasterr<0)return lasterr;  
  if(mat==NULL || dim==0){
    lasterr=ERR_PROG_NOT_MAT;
    fprintf(stderr,"Internal error #%i: Programmer, create matrix before using it in [calc]!\n",-lasterr);
    return lasterr;
  }
  unsigned int i,j,k;
  double coef;
  for(j=0;j<dim;j++){//проход всех строк
    if(MAT(j,j)==0){//диагональный элемент равен 0, непорядок, ищем ниже строки у которых он не равен нулю
      for(k=j+1;k<dim;k++)if(MAT(j,k)!=0)break;//проходим все нижележащие строки. Если элемент [j,k]!=0 то нашли
      if(MAT(j,k)==0 || k>=dim){//если ничего не нашли - решение неоднозначно - выводим ошибку
        lasterr=W_RES_NOT_UNIQ;
        fprintf(stderr,"Warning #%i: Coefficient at x^%i can not be calculated\n",lasterr,j);
        continue; //переход к следующей строке for(j=0;j<dim;j++)
      }
      for(i=j;i<=dim;i++){coef=MAT(i,k); MAT(i,k)=MAT(i,j); MAT(i,j)=coef;}//если нашли - меняем строки местами (начальные элементы все равно нули, чего их менять)
    }//все что левее диагонали все равно нулевое
    for(i=j+1;i<=dim;i++)MAT(i,j)=mult( MAT(i,j) , 1/MAT(j,j) );//делим всю строку на диагональный элемент
    MAT(j,j)=1;// x/x=1 полюбому
    for(k=0;k<dim;k++)if(k!=j){//проходим все строки кроме текущей
      coef=-MAT(j,k);
      MAT(j,k)=0;//зануляем все что на одной вертикали с текущим элементов. Оно все равно должно занулиться а нам считать меньше.
      for(i=j+1;i<=dim;i++)//проходим все элементы k-й строки и вычитаем из них j-ю умноженную на mat[j,k]
        MAT(i,k) = add( MAT(i,k) , mult( MAT(i,j) , coef) );
    }
  }
  return lasterr;
}

//вывод только коэффициентов начиная со старшего
int display_hval(FILE*fout){
  unsigned int i;
  char temp[52],*pos,lend='\n';
  if(lasterr<0)return lasterr;
  if(mat==NULL||dim==0){
    lasterr=ERR_PROG_NOT_MAT;
    fprintf(stderr,"Internal error #%i: Programmer, create matrix before using it in [display_hval]!\n",-lasterr);
    return lasterr;
  }
  if(fout==NULL){
    lasterr=ERR_PROG_FOUT;
    fprintf(stderr,"Internal error #%i: Programmer, create or open output file before using it!\n",-lasterr);
    return lasterr;
  }
  if(flag & FLAG_OLINE)lend='\t';
  for(i=dim-1;i!=(unsigned int)(-1);i--){
    //если стоит флаг вывода в экспоненциальной форме, выводим в ней с exp_len знаков после запятой   
    if(flag & FLAG_EXP)sprintf(temp,"%.*le%c",exp_len,MAT(dim,i),lend);else sprintf(temp,"%lf%c",MAT(dim,i),lend);
    //меняем десятичный разделитель с точки на dec_symb. Если он и так dec_symb не страшно - один раз заменит сам на себя
    //а больше десятичным разделителям взяться неоткуда  
    if((pos=strchr(temp,'.'))!=NULL)*pos=dec_symb;
    //вывод чере fputs чуть быстрее, чем через fprintf.
    fputs(temp,fout);
  }
  if(flag & FLAG_OLINE)fputs("\n",fout);
  return lasterr;
}

//вывод коэффициентов начиная с младшего
int display_lval(FILE*fout){
  unsigned int i;
  char temp[52],*pos,lend='\n';
  if(lasterr<0)return lasterr;
  if(mat==NULL||dim==0){
    lasterr=ERR_PROG_NOT_MAT;
    fprintf(stderr,"Internal error #%i: Programmer, create matrix before using it in [fillmat]!\n",-lasterr);
    return lasterr;
  }
  if(fout==NULL){
    lasterr=ERR_PROG_FOUT;
    fprintf(stderr,"Internal error #%i: Programmer, create or open output file before using it!\n",-lasterr);
    return lasterr;
  }
  if(flag & FLAG_OLINE)lend='\t';
  for(i=0;i<dim;i++){
    if(flag & FLAG_EXP)sprintf(temp,"%.*le%c",exp_len,MAT(dim,i),lend);else sprintf(temp,"%lf%c",MAT(dim,i),lend);
    if((pos=strchr(temp,'.'))!=NULL)*pos=dec_symb;
    fputs(temp,fout);
  }
  if(flag & FLAG_OLINE)fputs("\n",fout);
  return lasterr;
}

//вывод готового полинома
int display_poly(FILE*fout){
  unsigned int i;
  char temp[52],*pos;
  if(lasterr<0)return lasterr;
  if(mat==NULL||dim==0){
    lasterr=ERR_PROG_NOT_MAT;
    fprintf(stderr,"Internal error #%i: Programmer, create matrix before using it in [fillmat]!\n",-lasterr);
    return lasterr;
  }
  if(fout==NULL){
    lasterr=ERR_PROG_FOUT;
    fprintf(stderr,"Internal error #%i: Programmer, create or open output file before using it!\n",-lasterr);
    return lasterr;
  }
  fprintf(fout,"y = ");
  for(i=dim-1;i>1;i--){
    if(MAT(dim,i)!=0){
      sprintf(temp,"%lg x^%u + ",MAT(dim,i),i);
      if((pos=strchr(temp,'.'))!=NULL)*pos=dec_symb;
      fputs(temp,fout);
    }
  }
  if(dim>1){
    sprintf(temp,"%lg x + ",MAT(dim,i));
    if((pos=strchr(temp,'.'))!=NULL)*pos=dec_symb;
    fputs(temp,fout);
  }
  sprintf(temp,"%lg",MAT(dim,0));
  if((pos=strchr(temp,'.'))!=NULL)*pos=dec_symb;
  fputs(temp,fout);
  if(fout==stdout)printf("\n");
  return lasterr;
}
/*
 * прочие утилиты
 */

//Поиск следующего слова в строке, задаваемой src. Список разделителей передается в spl. Если строка внезапно кончилась - возвращает NULL
char *findnextword(char *src,const char *spl){
  char *res=src;
  while(strchr(spl,res[0])==NULL){if(res[0]==0)return NULL; res++;}//Ищем первый символ, являющийся разделителем (пропуск предыдущего слова)
  while(strchr(spl,res[0])!=NULL){if(res[0]==0)return NULL; res++;}//Ищем первый символ, не являющийся разделителем (пропуск разделителей между словами)
  return res;
}

//Чтение из входной строки X и Y координат в столбцах с номерами xpos и ypos
//  Если номер одного из столбцов меньше нуля - просто увеличиваем соответствующую координату
int readstr(char str[],const char splits[],int xpos,int ypos,double *x,double *y){
  //учитывая, что столбец Y может идти до столбца Х, а может после, заведем несколько переменных
  int min,max; //координата пеового столбца, координата второго столбца
  double *pmin,*pmax; //указатели на первый и второй столбец (чтобы проще было менять X и Y местами)
  int i;
  //подстроки для работы с исходной строкой
  char *ipos; //начало подстроки
  char *sres; //результат поиска резделителей

  if(lasterr<0)return lasterr;
  ipos=str;
  if(x==NULL || y==NULL)return 0;
  if(xpos<ypos){
    min=xpos; max=ypos; pmin=x; pmax=y;
  }else{
    min=ypos; max=xpos; pmin=y; pmax=x;
  }
  if(max<0)return 0; //оба номера столбцов отрицательные. Это неправильно
  //замена символа перевода строки концом строки. Честно говоря, без понятия зачем это надо
  i=strlen(str);
  if(i>0)if(str[i-1]=='\n')str[i-1]=0;
  if(i>1)if(str[i-2]=='\n')str[i-2]=0;
  
  i=0;
  //проверка, надо ли считывать значение из строки или просто увеличивать переменную
  if(min>=0){
    //пропуск (i-min-1) слов, то есть (min-1)
    for(;i<min;i++){
      ipos=findnextword(ipos,splits);
      if(ipos==NULL){
        lasterr=W_NOTNUM;
        fprintf(stderr,"Line %u: Warning #%i: There is not valid data in [%s] \n",linenum,lasterr,str);
        return lasterr;
      }
    }
    //замена десятичного разделителя на точку (если разделитель и так точка не страшно)
    sres=strchr(ipos,dec_symb);
    if(sres!=NULL)sres[0]='.';
    //"безопасный" вариант atof(). Точнее, позволяющий отследить ошибку во входных данных
    *pmin=strtod(ipos,&sres);
    if(sres!=NULL){
      if(sres==ipos){
        lasterr=W_NOTNUM;
        fprintf(stderr,"Line %u: Warning #%i: There is not valid data in [%s] \n",linenum,lasterr,str);
        return lasterr;
      }
    } 
  }else(*pmin)++;
  //пропуск (i-max-1) строк, то есть (max-min-1)
  for(;i<max;i++){
   ipos=findnextword(ipos,splits);
   if(ipos==NULL){
    lasterr=W_NOTNUM;
    fprintf(stderr,"Line %u: Warning #%i: There is not valid data in [%s] \n",linenum,lasterr,str);
    return lasterr;
   }
  }
  //замена десятичного разделителя и преобразование в число (см. выше)
  sres=strchr(ipos,dec_symb);
  if(sres!=NULL)sres[0]='.';
  *pmax=strtod(ipos,&sres);
  if(sres!=NULL){
   if(sres==ipos){
    lasterr=W_NOTNUM;
    fprintf(stderr,"Line %u: Warning #%i: There is not valid data in [%s] \n",linenum,lasterr,str);
   }
  }
  return lasterr;
}

//вывод матрицы (только для отладки)
void outmat(){
  unsigned int i,j,r=0;
  if(lasterr<0)return;
  for(j=0;j<dim;j++){
    for(i=0;i<=dim;i++){
      printf("%.2f\t",mat[r]);
      r++;
    }
    printf("\n");
  }
}

//Расчет точности аппроксимации (скорее всего, неправильный)
int display_sq(FILE *fin,FILE *fout){
  double x=-1,y1,y2,resval=0,i,num=0;
  int res;
  double *m,minY=0,maxY=0;
  char str[255]="";
  if(lasterr<0)return lasterr;
  if(mat==NULL||dim==0){
    lasterr=ERR_PROG_NOT_MAT;
    fprintf(stderr,"Internal error #%i: Programmer, create matrix before using it in [display_sq]!\n",-lasterr);
    return lasterr;
  }
  if(fout==NULL){
    lasterr=ERR_PROG_FOUT;
    fprintf(stderr,"Internal error #%i: Programmer, create or open output file before using it!\n",-lasterr);
    return lasterr;
  }
  if(fin==NULL){
    lasterr=ERR_NOT_IFILE;
    fprintf(stderr,"Internal error #%i: Programmer, create or open input file before using it!\n",-lasterr);
    return lasterr;
  }
  do{
    res=(NULL!=fgets(str,255,fin));
    readstr(str,splitchars,xpos,ypos,&x,&y1);
    if(res){
      if(num==0){
        minY=y1; maxY=y1;
      }else{
        if(minY>y1)minY=y1;
        if(maxY<y1)maxY=y1;
      }
      num++;
      m=&(mat[dim*dim+dim-1]);
      y2=0;
      for(i=0;i<dim;i++){
        y2=*m+y2*x;
        m-=(dim+1);
      }
      resval+=(y2-y1)*(y2-y1);
    }else break;
  }while(1);
  fprintf(fout,"%le\n",resval);
  return 0;
 }

//как ни странно эта процедура отображает подсказку
void help(){
  printf("Program to calculate the polynomial function nearest to input array of points\n");
  printf("Input format: file containing columns of X and Y values\n");
  printf("Output format: coefficientes of polynome according output format flags\n");
  printf("Version %i.%i\n\n",version_1,version_2);
  printf("-h - display this help\n");
  printf("-p - display result as polynome (default)\n");
  printf("-v - display result as values (from low power to high)\n");
  printf("-V - display result as values (from high power to low)\n");
  printf("-P - do not display result\n");
  printf("-c - echo read data and input error\n");
  printf("-t - output (f(x)-y)^2. WARNING! need to re-read input file\n");
  printf("-l - output all coefficients to a single line\n");
  printf("-L [str] - output [str] before result\n");
  printf("-e - exponential form of output\n");
  printf("-E [count] - exponential form, [count] digits after decimal point\n"); 
  printf("-d [char] - symbol of decimal dot (real dot is also used)\n"); 
  printf("-m [int] - maximum power of polynome\n");
  printf("-X [num] - position of 'X' column (-1 means increment from s to max)\n");
  printf("-Y [num] - position of 'Y' column (-1 means increment from s to max)\n");
  printf("-s [num] - start value of 'X' or 'Y' column if its position negative (default = 0)\n");
  printf("-S [num] - skip [num] lines of input\n"); 
  printf("-i [filename] - input filename (default - keyboard, end of input = ^D)\n");
  printf("-o [filename] - output filename (default - screen)\n");
  printf("-r [min],[max] - use points with X coordinate in rangle [min...max] and ignore other\n");
  printf("-R [min],[max] - use points with Y coordinate in rangle [min...max] and ignore other\n");
  printf("For example, options -R 2,3 and -r \"2 3\" are correct, but not -r 2 3 or -R \"2,5 3\"\n"); 
}

int main(int argc,char **argv){
  FILE *fin=stdin,*fout=stdout;//а вдруг мы захотим писать не в консоль а в файл? Перенаправление ввода-вывода не всегда удобно
  double x=-1,y=-1;//сами точки хранить нет надобности но вот без текущей не обойтись
  int res=1;//это только для ввода из файла, больше нигде не используется
  char str[1024];
  char *pref=NULL;

  dim=1;//по умолчанию будем считать среднее арифметическое
  flag |= FLAG_POLY;//по умолчанию вывод в форме полинома
  flag = FLAG_POLY;
  while((res=getopt(argc,argv,":m:i:o:hpvVcd:eE:tX:Y:S:Plr:R:s:L:"))!=-1){
    switch(res){
      case 'm':
        res=strtol(optarg,(char**)NULL,0);
        if(errno==ERANGE || res<0){
          lasterr=W_WRONG_ATTR_M;
          fprintf(stderr,"Warning #%i: [%s] is incorrect value of max power; using default value [%i]\n",lasterr,optarg,dim-1);
        }else dim=res+1;
        break;
      case 'i':
        fin=fopen(optarg,"rt");
        if(fin==NULL){
          lasterr=ERR_NOT_IFILE;
          fprintf(stderr,"Error #%i: Can not open input file [%s]\n",-lasterr,optarg);
          fin=stdin;
          flag |= FLAG_EXIT;
        }
        break;
      case 'o':
        fout=fopen(optarg,"wt");
        if(fout==NULL){
          lasterr=W_NOT_OFILE;
          fprintf(stderr,"Warning #%i: Can not create output file [%s]; using console output\n",lasterr,optarg);
          fout=stdout;
        }
        break;
      case 'h': flag|=FLAG_EXIT; help(); break;
      case 'p': flag &= ~FLAG_MASK_VAL; flag|=FLAG_POLY; break;
      case 'v': flag &= ~FLAG_MASK_VAL; flag|=FLAG_LVAL; break;
      case 'V': flag &= ~FLAG_MASK_VAL; flag|=FLAG_HVAL; break;
      case 'P': flag &= ~FLAG_MASK_VAL; flag|=FLAG_NONE; break;
      case 'c': flag |= FLAG_ECHO;  break;
      case 'd': dec_symb=optarg[0]; break;
      case 'e': flag |= FLAG_EXP; break;
      case 'E':
        res=strtol(optarg,(char**)NULL,0);
        if(errno==ERANGE || res<1){
          lasterr=W_WRONG_ATTR_M;
          fprintf(stderr,"Warning #%i: [%s] is incorrect length of exponent values; using default value [%i]\n",lasterr,optarg,exp_len);
        }else{exp_len=res; flag |= FLAG_EXP;}
        break;
      case 't': flag |= FLAG_TEST; break;
      case 'X':
        res=strtol(optarg,(char**)NULL,0);
        if(errno==ERANGE){
          lasterr=W_WRONG_ATTR_M;
          fprintf(stderr,"Warning #%i: [%s] is incorrect column number of X values; using default value [%i]\n",lasterr,optarg,xpos);
        }else xpos=res;
        break;
      case 'Y':
        res=strtol(optarg,(char**)NULL,0);
        if(errno==ERANGE){
          lasterr=W_WRONG_ATTR_M;
          fprintf(stderr,"Warning #%i: [%s] is incorrect column number of Y values; using default value [%i]\n",lasterr,optarg,ypos);
        }else ypos=res;
        break;
      case 'S':
        res=strtol(optarg,(char**)NULL,0);
        if(errno==ERANGE || res<0){
          lasterr=W_WRONG_ATTR_M;
          fprintf(stderr,"Warning #%i: [%s] is incorrect number of skipped lines; using default value [%i]\n",lasterr,optarg,fskip);
        }else fskip=res;
        break;
      case 'l': flag |= FLAG_OLINE; break;
      case 'r': readstr(optarg,", \t\n\0",0,1,&xmin,&xmax); break;
      case 'R': readstr(optarg,", \t\n\0",0,1,&ymin,&ymax); break;
      case 's':
        res=strtol(optarg,(char**)NULL,0); res-=1;
        if(errno==ERANGE){
          lasterr=W_WRONG_ATTR_M;
          fprintf(stderr,"Warning #%i: [%s] is incorrect start value for X or Y\n",lasterr,optarg);
        }else if(xpos<0)x=res;else if(ypos<0)y=res; else{
        lasterr=W_WRONG_ATTR_M;
        fprintf(stderr,"Warning #%i: Can not set start value for X or Y because they both will be read directly\n",lasterr);
        }
        break;
      case 'L': pref=optarg; break;
      default: lasterr=W_UNDEF_FLAG; fprintf(stderr,"Warning #%i: [-%c] is incorrect option\n",lasterr,optopt);
    }//switch
  }//while
  //если взведен флаг FLAG_EXIT сразу выходим
  if(flag & FLAG_EXIT){fclose(fin); fclose(fout); return 0;}
  //инициализация матрицы
  mat=(double*)malloc((dim*dim+dim)*sizeof(double));
  if(mat==NULL){
    lasterr=ERR_NOT_SPACE;
    fprintf(stderr,"Error #%i: Not enough space in RAM\n",lasterr);
    return lasterr;
  }
  if(clearmatrix()<0)return lasterr;
  //пропуск нескольких строк перед началом чтения данных
  for(;fskip>0;fskip--){fgets(str,1024,fin);linenum++;}  
  //чтение данных из файла
  do{
    res=(NULL!=fgets(str,1024,fin)); //чтение строки из файла
    if(res){
      res=readstr(str,splitchars,xpos,ypos,&x,&y); //ее парсинг специальной функцией (см. выше)
      linenum++;
      if(x>=xmin && x<=xmax && y>=ymin && y<=ymax && res!=W_NOTNUM){ //проверка попадания в разрешенный диапазон
        res=appendmatrix(x,y);
        if(flag & FLAG_ECHO)printf("%lf\t%lf\n",x,y);    
      }else res=0;
      if(lasterr==W_NOTNUM){lasterr=0; res=0;}//если возникла ошибка некорректных данных в одной строке - игнорируем
      if(res<0){fclose(fin); fclose(fout); free(mat); return lasterr;} //а вот если что-то серьезное или просто кончился файл - выходим
    }else break;
  }while(1);
  //дозаполнение матрицы и вычисление корней
  fillmat();
  calc();
  //проверка качества аппроксимации (если разрешена)
  if(flag & FLAG_TEST){
   rewind(fin);
   if(fin==NULL){
    lasterr=ERR_NOT_IFILE;
    fprintf(stderr,"Error #%i: Can not open input file!\n",-lasterr);
    return lasterr;
   }
   display_sq(fin,fout);
  }
  //если надо - вывод префикса - заданного снаружи текста (удобно!)
  if(pref!=NULL){
   fputs(pref,fout);
   if(flag & FLAG_OLINE)fputs("\t",fout);else fputs("\n",fout);
  }
  //вывод в соответствии с выбранным форматом
  switch(flag & FLAG_MASK_VAL){
   case FLAG_HVAL: display_hval(fout); break;
   case FLAG_LVAL: display_lval(fout); break;
   case FLAG_POLY: display_poly(fout); break;
   default:;
  }
  fclose(fin);
  fclose(fout);
  free(mat);
  return lasterr;
}
/* Описание математической модели (в формате LaTeX)
\documentclass[12pt]{article}
\usepackage[utf8]{inputenc} % Включаем поддержку UTF8
\usepackage[russian]{babel} % указать, что язык текста - русский
\usepackage{amsmath}
\title{}

\begin{document}
\section{Математическая модель}
В общем виде полином степени N может быть представлен в следующей форме
\[ y=\sum_{i=0}^{N}{a_i x^i} \]
Метод наименьших квадратов основан на том, что сумма квадратов разности вычисленного по формуле значения и введенного должна быть минимальна. Сумма квадратов для набора из M пар чисел записывается так:
\[ f = \sum_{m=1}^{M}(y(x_m)-y_m)^2 = \sum_{m=1}^{M}(\sum_{i=0}^{N}{a_i x_m^i} - y_m)^2 \]
Минимуму данной функции соответствует точка, где частные производные по всем переменным (переменными считаются аргументы $a_i$) равны нулю: $\partial f / \partial a_j = 0$. Запишем уравнение частной производной:
\[ \frac{\partial f}{\partial a_j} = \frac{\partial \sum_{m=1}^{M}(\sum_{i=0}^{N}{a_i x_m^i}-y_m)^2}{\partial a_j}  \]
По правилу дифференцирования сложных функций
\[ \frac{\partial f}{\partial a_j} = \sum_{m=1}^{M}2(\sum_{i=0}^{N}{a_i x_m^i}-y_m)\frac{\partial \sum_{i=0}^{N}{a_i x_m^i}}{\partial a_j} \]
Рассмотрим последний множитель отдельно:
\[ \frac{\partial \sum_{i=0}^{N}{a_i x^i}}{\partial a_j} = \sum_{i=0}^{N}\frac{\partial a_i x^i}{\partial a_j} \]
Очевидно, что частная производная каждого слагаемого, кроме $a_j x^j$, равна нулю, а производная этого слагаемого равна $x^j$. Воспользуемся этим:
\begin{eqnarray*}
 \frac{\partial f}{\partial a_j} = 2\sum_{m=1}^{M}(\sum_{i=0}^{N}{a_i x_m^i}-y_m)x_m^j = \\
= 2\sum_{m=1}^{M}(\sum_{i=0}^{N}{a_i x_m^{i+j}} - y_m x_m^j ) = \\
= 2( \sum_{m=1}^{M}\sum_{i=0}^{N}{a_i x_m^{i+j}} - \sum_{m=1}^{M}{y_m x_m^j} ) = \\
= 2( \sum_{i=0}^{N}a_i\sum_{m=1}^{M}x_m^{i+j} - \sum_{m=1}^{M}{y_m x_m^j} )
\end{eqnarray*}
Учитывая равенство частных производных нулю, для каждого $a_j$ можно записать равенство
\[ \sum_{i=0}^{N}a_i\sum_{m=1}^{M}x_m^{i+j} = \sum_{m=1}^{M}{y_m x_m^j} \]
Заметим, что входные параметры ($x_m, y_m$) входят только в виде сумм отдельных точек и не зависят от остальных. Это значит, что добавлять данные в матрицу можно по одной точке, храня только промежуточные значения. Введем обозначения
\begin{eqnarray*} \sum_{m=1}^{M}x_m^{i+j} = X^{i+j} \\
\sum_{m=1}^{M}{y_m x_m^j} = Y^j
\end{eqnarray*}
Для наглядности можно представить это равенство в виде системы N линейных уравнений с N неизвестных:
\begin{eqnarray*}
a_0 X^{0+0} + a_1 X^{1+0} + ... + a_N X^{N+0} = Y^0 \\
a_0 X^{0+1} + a_1 X^{1+1} + ... + a_N X^{N+1} = Y^1 \\
...\\
a_0 X^{0+N} + a_1 X^{1+N} + ... + a_N X^{N+N} = Y^N
\end{eqnarray*}
Существует множество способов решения такой системы. Я выбрал достаточно простой - приведение соответствующей матрицы к единичной
\[
\begin{bmatrix}
X^{0+0} & X^{1+0} & ... & X^{N+0} & Y^0 \\
X^{0+1} & X^{1+1} & ... & X^{N+1} & Y^1 \\
...     & ...     & ... & ...     & ... \\
X^{0+N} & X^{1+N} & ... & X^{N+N} & Y^N
\end{bmatrix}
\]
Результатом будет являться массив значений $a_j$, то есть искомых коэффициентов полинома.
\section{Немного об оптимизации}
  Расчет аппроксимации состоит из двух этапов (не считая анализ ключей запуска, форматирования вывода, контроля ошибок и прочего): заполнение матрицы данными и расчет коэффициентов.
  Легко заметить, что элементы матрицы вдоль побочных диагоналей равны, поэтому на этапе заполнения матрицы меняются только элементы в первой строке и в двух правых столбцах. После этого, в начале этапа расчета, эти данные копируются в остальные ячейки на соответствующих диагоналях.
  Тот факт, что каждый элемент представляет собой просто сумму координат каждой точки, возведенных в определенную степень, дает возможность заполнять матрицу на потоке вместо того чтобы хранить все введенные данные. Не то чтобы я боялся переполнения памяти, но это лишние сложности с выделением-освобождением, а значит лишний шанс допустить ошибку. Ну и использование памяти только под матрицу - приятный бонус.
  Сложность добавления новой точки к матрице O(N), что довольно неплохо
  Сложность расчета коэффициентов $O(N^3)$, что уже не так радужно. Впрочем, на пратике редко требуется считать полиномы больше 3-й степени, так что я не считаю это серьезной проблемой. Важно что сложность этого этапа не зависит от количества точек, только от степени полинома. Это значит, что апроксимация полиномом низкой степени будет достаточно быстрой и экономной по памяти даже для больших наборов данных. Это не может не радовать.
\end{document}
*/
