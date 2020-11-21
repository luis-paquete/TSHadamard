/*
  Chiarandini, M.; Kotsireas, I. S.; Koukouvinos, C. & Paquete,
  L. Heuristic algorithms for Hadamard matrices with two circulant cores
  Theoretical Computer Science, to appear, 2008
  http://dx.doi.org/10.1016/j.tcs.2008.06.002
*/


#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <assert.h>
#include <math.h>
#include <limits.h>
#include <libgen.h>

#define VERBOSE(X);

#define norm   2.328306549295728e-10
#define m1     4294967087.0
#define m2     4294944443.0
#define a12          1403580.0
#define a13n            810728.0
#define a21             527612.0
#define a23n          1370589.0

int ell;
static double  s10, s11, s12, s20, s21, s22;

/* Random Generator by Pierre L'Ecuyer */
double MRG32k3a()
{
   long    k;
   double p1, p2;
   /* Component 1 */
   p1 = a12 * s11 - a13n * s10;
   k = p1 / m1;
   p1 -= k * m1;  
   if (p1 < 0.0) p1 += m1;
   s10 = s11; s11 = s12; s12 = p1;
   /* Component 2 */
   p2 = a21 * s22 - a23n * s20;
   k = p2 / m2; p2 -= k * m2;
   if (p2 < 0.0) p2 += m2;
   s20 = s21; s21 = s22; s22 = p2;
   /* Combination */
   if (p1 <= p2) return ((p1 - p2 + m1) * norm);
   else return ((p1 - p2) * norm);
}


double ranU01(void)
{
   return MRG32k3a();
}

/* Uniform random int in [i,j] */
int ranUint(int i, int j)
{
   return i + (int) ((j - i + 1.0) * MRG32k3a());
}



/* Floored division */
/* returns  x - ell * ((int) floor((double) (x)/ell)) */
int divF( int D, int d )
{
  int q = D/d;
  int r = D%d;
  if ((r > 0 && d < 0) || (r < 0 && d > 0)) q = q-1;
  return q;
}
int modF( int D, int d )
{
  int r = D%d;
  if ((r > 0 && d < 0) || (r < 0 && d > 0)) r = r+d;
  return r;
}



void UpdateTabu(int **tabu, int i1, int i2, int iter, int tabu_tenure ) {
  //  tabu[i2][i1] = iter+tabu_tenure;
  tabu[i1][i2] = iter+tabu_tenure;
}


int Obj(int *A,int *B,int *PA, int *PB) {
  
  int F;
  int s, i;

  F=0;
  for (s=1; s<=(ell-1)/2; s++)
    {
      PA[s]=0;
      PB[s]=0;
      for (i=0; i<ell; i++)
	{
	  PA[s] += A[i] * A[(i+s) % ell];
	  PB[s] += B[i] * B[(i+s) % ell];
	}
      F += abs(2+PA[s]+PB[s]);
      //      printf("PA[%d]: %d PB[%d]: %d\n",s,PA[s],s,PB[s]);
    }
  return F;
}



int Check(int *A, int *B) {
  
  int F;
  int s,pa,pb, i;

  pa=pb=0;
  for (i=0; i<ell; i++)
    {
      pa += A[i];
      pb += B[i];
    }
  assert(pa==1 && pb==1);
  F=0;
  for (s=1; s<=(ell-1)/2; s++)
    {
      pa=0;
      pb=0;
      for (i=0; i<ell; i++)
	{
	  pa += A[i]*A[(i+s) % ell];
	  pb += B[i]*B[(i+s) % ell];
	}
      //printf("PA[%d]: %d PB[%d]: %d\n",s,pa,s,pb);
      F += abs(2+pa+pb);
    }
  return F;
}


int New(int *C,int i1, int i2,int *PA, int *PB)
{
  int s, tmp,new_PA,new=0;
  //printf("-->I1 %d I2 %d | %d %d\n",i1,i2,A[i1],A[i2]);
  for (s=1; s<=(ell-1)/2; s++)
    {
      if (s==i2-i1)
	{
	  tmp = C[i2] * C[modF(i2+s,ell)] + C[modF(i1-s,ell)] * C[i1];
	  //  printf("%d: (%d,%d)(%d,%d) ",s,i2,j2,j1,i1);
	  //printf("\t PA[%d]: %d -> %d\n",s,PA[s],PA[s]-2*tmp);
	  new_PA = abs(2+PA[s]-2*tmp+PB[s]);
	  new += new_PA;
	}
      else if (s==ell-i2+i1)
	{
	  tmp = C[i1] * C[modF(i1+s,ell)] +  C[modF(i2-s,ell)] * C[i2];
	  //printf("%d: (%d,%d)(%d,%d) ",s,i1,j2,j1,i2);	  
	  //printf("\t PA[%d]: %d -> %d\n",s,PA[s],PA[s]-2*tmp);
	  new_PA = abs(2+PA[s]-2*tmp+PB[s]);
	  new += new_PA;
	}
      else
	{
	  tmp =  C[i1] * C[modF(i1+s,ell)] + C[modF(i1-s,ell)] * C[i1];
	  //printf("%d %d %d %d\n",C[i1], C[j2], C[j1], C[i1]);
	  //printf("%d: %d (%d,%d)(%d,%d) ",s,tmp,i1,j2,j1,i1);
	  tmp +=  C[i2] * C[modF(i2+s,ell)] + C[modF(i2-s,ell)] * C[i2];
	  //printf("%d: %d (%d,%d)(%d,%d) ",s,tmp,i2,j2,j1,i2);
	  //printf("\t PA[%d]: %d -> %d\n",s,PA[s],PA[s]-2*tmp);
	  new_PA = abs(2+PA[s]-2*tmp+PB[s]);
	  new += new_PA;
	}
    }

  return new;
}


void Make(int *C,int *P,int i1, int i2)
{
  int s,tmp;
  for (s=1; s<=(ell-1)/2; s++)
    {
      if (s==(i2-i1))
	{
 	  tmp = C[i2] * C[modF(i2+s,ell)] + C[modF(i1-s,ell)] * C[i1];
	  P[s] -= 2*tmp;
	}
      else if (s==(ell-i2+i1))
	{
	  tmp = C[i1] * C[modF(i1+s,ell)] +  C[modF(i2-s,ell)] * C[i2];
	  P[s] -= 2*tmp; 
	  
	}
      else
	{
	  tmp =  C[i1] * C[modF(i1+s,ell)] + C[modF(i1-s,ell)] * C[i1];
	  tmp +=  C[i2] * C[modF(i2+s,ell)] + C[modF(i2-s,ell)] * C[i2];
	  P[s] -= 2 * tmp;
	}
    }
  C[i1]=(-1) * C[i1];
  C[i2]=(-1) * C[i2];
}


void Init(int *A, int *B){
  int tmp,i,r;

  for (i = 0; i<(ell+1)/2; i++)
    A[i]=B[i]=1;
  for (; i<ell; i++)
    A[i]=B[i]=-1;
    
  for (i = ell-1; i > 0; i--) {
    r =ranUint(0,i);
    //assert(r<=i && r>=0);
    tmp = A[i]; A[i] = A[r]; A[r] = tmp;
  }
  for (i = ell-1; i > 0; i--) {
    r =ranUint(0,i);
    //assert(r<=i && r>=0);
    tmp = B[i]; B[i] = B[r]; B[r] = tmp;
  }

}


void PrintSol(FILE *sol_file,int *A,int *B){

  int i;
  for (i=0;i<ell;i++)
    if (A[i] == 1)
      fprintf(sol_file,"1,");
    else
      fprintf(sol_file,"-1,");
  for (i=0;i<ell;i++)
    if (B[i] == 1)
      fprintf(sol_file,"1,");
    else
      fprintf(sol_file,"-1,");
  fseek(sol_file,-1,SEEK_CUR);
  fprintf(sol_file,"\n");
  fflush(sol_file);

  for (i=0;i<ell;i++)
    if (A[i] == 1)
      printf("+");
    else
      printf("-");
  printf("   ");
  for (i=0;i<ell;i++)
    if (B[i] == 1)
      printf("+");
    else
      printf("-");
  printf("\n");
}



int main(int argc, char *argv[]) {

  int *A;
  int *B;
  int *PA;
  int *PB;
  int **tabuA;
  int **tabuB;
  int tabu_tenure;

  int best, best_all;
  int i,j;
  time_t s_init, s_end;
  int new,current=0;
  FILE * sol_file;
  unsigned int max_time;
  int iter, noimpr;
  int i1,i2,move_i1=0,move_i2=0;
  char buf[30];

  if (argc!=6)
    {
      fprintf(stderr, "Tabu search to find circulant cores\n");
      fprintf(stderr, "for the construction of Hadamard matrices\n");
      fprintf(stderr, "(Authors: marco@imada.sdu.dk,  paquete@dei.uc.pt)\n\n");
      fprintf(stderr, "Usage:\n");
      fprintf(stderr, "      %s requires the following parameters (in the given order):\n",argv[0]);
      fprintf(stderr, "      (1) ell (the size of the sequence. n=ell*2+2.) \n");
      fprintf(stderr, "      (2) max_time (time limit in seconds)\n");
      fprintf(stderr, "      (3) random_seed\n");
      fprintf(stderr, "      (4) riter (idle iterations before restart)\n");
      fprintf(stderr, "      (5) tabu_tenure (multiplier of ell)\n");
      fprintf(stderr, "When a solution is found it is printed in the standard output\n");
      fprintf(stderr, "and in a file with name: sol-exe-(1)-(2)-(3)-(4)-(5).txt\n\n");

      exit(EXIT_FAILURE);
    }

  ell = atol(argv[1]);
  max_time = atol(argv[2]);
  s10=s11=s12=s20=s21=s22=atoi(argv[3]);
  sprintf(buf,"sol-%s-%s-%s-%s-%s-%s.txt",basename(argv[0]),argv[1],argv[2],argv[3],argv[4],argv[5]);
  sol_file = fopen(buf,"w");
    
  if (sol_file==NULL)
        {
        printf("problems in opening file\n");
        exit(1);
        }


  time(&s_init);
  
  tabu_tenure=ell*atof(argv[5]);

  PA=malloc((ell+1)/2 * sizeof(int));
  PB=malloc((ell+1)/2 * sizeof(int));
    
  A = malloc(ell * sizeof(int));
  B = malloc(ell * sizeof(int));

  tabuA = malloc(ell * sizeof(int *));
  tabuB = malloc(ell * sizeof(int *));
  for (i = 0; i < ell; i++)
    {
      tabuA[i] = malloc(ell * sizeof(int));
      tabuB[i] = malloc(ell * sizeof(int));
      for (j = 0; j < ell; j++)
	{
	  tabuA[i][j] = 0;
	  tabuB[i][j] = 0;
	}
    }


  iter=1;
  while (1) {
    VERBOSE(printf("RESTART\n");)
    Init(A,B);
    best_all = current = Obj(A,B,PA,PB);  
    noimpr=0;
    //assert(current==Check(A,B));
    while (1) {
    
      /*------2 exchange first half ------*/ 
      best=INT_MAX;
      for (i1 = 0; i1 < ell-1; i1++) {
	for (i2 = i1+1; i2 < ell; i2++) {
	  if (A[i1]!=A[i2])
	    {
	      new = New(A,i1,i2,PA,PB);
	      if (((new < best) && (tabuA[i1][i2]<iter)) ||
		  (new<best_all) ) {
		best = new;
		move_i1 = i1;
		move_i2 = i2;
	      }
	    }
	}
      }

      Make(A,PA,move_i1,move_i2);
      current = best;
      if (current < best_all)
	{
	  best_all = current;	      	
	  noimpr=0;
	  VERBOSE(printf("A: best: %i new: %i [%i,%i] \n",best_all,current,move_i1,move_i2);)
	}
      else
	noimpr++;
      if (current == 0)
	{
	  time(&s_end);
	  printf("FOUND SOLUTION AT TIME: %.2f\n",(double) (s_end - s_init)); 
	  PrintSol(sol_file,A,B);
	  break;
	}
      UpdateTabu(tabuA,move_i1,move_i2,iter++,tabu_tenure);

      //assert(current == Check(A,B));
 
      /*------2 exchange second half ------*/ 
    
      best = INT_MAX;
      for (i1 = 0; i1 < (ell-1); i1++) {
	for (i2 = i1+1; i2 < ell; i2++) {
	  if (B[i1]!=B[i2])
	    {
	      new = New(B,i1,i2,PA,PB);
	      if (((new < best) && (tabuB[i1][i2]<iter)) ||
		  new<best_all) {
		best = new;
		move_i1 = i1;
		move_i2 = i2;
	      }
	    }
	}
      }
      Make(B,PB,move_i1,move_i2);
      current = best;
      if (current < best_all)
	{
	  best_all = current;	      	
	  noimpr=0;
	  VERBOSE(printf("B: best: %i new: %i [%i,%i] %.2f\n",best_all,current,move_i1,move_i2,(double) (s_end - s_init));)
	}
      else
	noimpr++;
      if (current == 0)
	{
	  time(&s_end);
	  printf("FOUND SOLUTION AT TIME: %.2f\n",(double) (s_end - s_init)); 
	  PrintSol(sol_file,A,B);
	  break;
	}
      UpdateTabu(tabuB,move_i1,move_i2,iter++,tabu_tenure);
    
      time(&s_end);
    
      //assert(current == Check(A,B));
    
      //printf("%i %i %i \n",flag, best,best_all);

      if (noimpr>atoi(argv[4]))
	break;

      if (s_end > s_init + max_time)
	{
	  fclose(sol_file);
	  return 1;
	}
    }
  }
  fclose(sol_file);
  return 1;
}
