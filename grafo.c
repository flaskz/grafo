#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <graphviz/cgraph.h>

#include "grafo.h"

#define TAMRT 1000 //maximo de rotulos

static int busca_aresta(Agedge_t *g,lista l);
static vertice busca_vertice(char *nome, grafo g);
static void guarda_in(Agraph_t *g, Agnode_t *v,lista l);
static void guarda_out(Agraph_t *g, Agnode_t *v,lista l);
static lista guarda_arestas(Agraph_t *g, Agnode_t *v,lista l);
static lista ajeita_vertices(Agraph_t *g,int direcionado);
static void cria_aresta(Agedge_t *a,lista l);
static void salva_aresta(vertice v,lista l);
static int destroi_vertice(void *ptr);
static int destroi_aresta(void *ptr);
static int remove_vert(char *nome, grafo g);
static int maior_rt(vertice v1, vertice v2, int i);
static int busca_caminho(vertice v, lista l, int last, grafo g);
static lista caminho_aumentante(grafo g);
static int desvisita_vertices(grafo g);
static void xor(lista l, grafo g);

struct grafo{
  char *nome;
  int direcionado;
  int ponderado;
  lista vert;
  unsigned int n_vertices;
  unsigned int n_arestas;
};

struct vertice {
  char *nome;
  int visitado;
  int coberto;
  unsigned int rotulo[TAMRT];
  lista arest_in;
  lista arest_out;
};

struct aresta {
  long int peso;
  //emparelhamento?
  int coberta;
  char *origem;
  char *destino;
};

typedef struct aresta *aresta;

static int acha_aresta(aresta g,lista l);

//funcoes lista

//---------------------------------------------------------------------------
// nó de lista encadeada cujo conteúdo é um void *

struct no {

  void *conteudo;
  no proximo;
};
//---------------------------------------------------------------------------
// lista encadeada

struct lista {
  
  unsigned int tamanho;
  int padding; // só pra evitar warning 
  no primeiro;
};
//---------------------------------------------------------------------------
// devolve o número de nós da lista l

unsigned int tamanho_lista(lista l) { return l->tamanho; }

//---------------------------------------------------------------------------
// devolve o primeiro nó da lista l,
//      ou NULL, se l é vazia

no primeiro_no(lista l) { return l->primeiro; }

//---------------------------------------------------------------------------
// devolve o conteúdo do nó n
//      ou NULL se n = NULL 

void *conteudo(no n) { return n->conteudo; }

//---------------------------------------------------------------------------
// devolve o sucessor do nó n,
//      ou NULL, se n for o último nó da lista

no proximo_no(no n) { return n->proximo; }

//---------------------------------------------------------------------------
// cria uma lista vazia e a devolve
//
// devolve NULL em caso de falha

lista constroi_lista(void) {

  lista l = malloc(sizeof(struct lista));

  if ( ! l ) 
    return NULL;

  l->primeiro = NULL;
  l->tamanho = 0;

  return l;
}
//---------------------------------------------------------------------------
// desaloca a lista l e todos os seus nós
// 
// se destroi != NULL invoca
//
//     destroi(conteudo(n)) 
//
// para cada nó n da lista. 
//
// devolve 1 em caso de sucesso,
//      ou 0 em caso de falha

int destroi_lista(lista l, int destroi(void *)) { 
  
  no p;
  int ok=1;

  while ( (p = primeiro_no(l)) ) {
    
    l->primeiro = proximo_no(p);

    if ( destroi )
      ok &= destroi(conteudo(p));

    free(p);
  }

  free(l);

  return ok;
}
//---------------------------------------------------------------------------
// insere um novo nó na lista l cujo conteúdo é p
//
// devolve o no recém-criado 
//      ou NULL em caso de falha

no insere_lista(void *conteudo, lista l) { 

  no novo = malloc(sizeof(struct no));

  if ( ! novo ) 
    return NULL;

  novo->conteudo = conteudo;
  novo->proximo = primeiro_no(l);
  ++l->tamanho;
  
  return l->primeiro = novo;
}

//------------------------------------------------------------------------------
// remove o no de endereço rno de l
// se destroi != NULL, executa destroi(conteudo(rno)) 
// devolve 1, em caso de sucesso
//         0, se rno não for um no de l

int remove_no(struct lista *l, struct no *rno, int destroi(void *)) {
	int r = 1;
	if (l->primeiro == rno) {
		l->primeiro = rno->proximo;
		if (destroi != NULL) {
			r = destroi(conteudo(rno));
		}
		free(rno);
		l->tamanho--;
		return r;
	}
	for (no n = primeiro_no(l); n->proximo; n = proximo_no(n)) {
		if (n->proximo == rno) {
			n->proximo = rno->proximo;
			if (destroi != NULL) {
				r = destroi(conteudo(rno));
			}
			free(rno);
			l->tamanho--;
			return r;
		}
	}
	return 0;
}

//fim funcoes lista


char *nome_grafo(grafo g){
  return g->nome;
}

int direcionado(grafo g){
  return (g->direcionado);
}

int ponderado(grafo g){
  return g->ponderado;
}

char *nome_vertice(vertice v){
  return v->nome;
}

unsigned int n_vertices(grafo g){
  return g->n_vertices;
}

unsigned int n_arestas(grafo g){
  return g-> n_arestas;
}

long int aresta_peso(aresta a){
  return a->peso;
}

static int busca_aresta(Agedge_t *g,lista l){

  for ( no n=primeiro_no(l); n; n=proximo_no(n)) {
    Agedge_t *a = conteudo(n);
    if ( ageqedge(g, a) )
      return 1;
  }

  return 0;
}

static void guarda_in(Agraph_t *g, Agnode_t *v,lista l) {

  for (Agedge_t *a=agfstin(g,v); a; a=agnxtin(g,a))
    if ( ! busca_aresta(a,l) &&  strcmp(agnameof(aghead(a)),agnameof(v)) == 0)
      cria_aresta(a,l);
}

static void guarda_out(Agraph_t *g, Agnode_t *v,lista l) {

  for (Agedge_t *a=agfstout(g,v); a; a=agnxtout(g,a))

    if ( ! busca_aresta(a,l) &&  strcmp(agnameof(agtail(a)),agnameof(v)) == 0)
      cria_aresta(a,l);

}

static lista guarda_arestas(Agraph_t *g, Agnode_t *v,lista l) {

  for (Agedge_t *a=agfstedge(g,v); a; a=agnxtedge(g,a,v))

    if ( ! busca_aresta(a,l) )

      cria_aresta(a,l);

  return l;
}

static lista ajeita_vertices(Agraph_t *g,int direcionado){
  lista lista_vertices = constroi_lista();

  for (Agnode_t *v=agfstnode(g); v; v=agnxtnode(g,v)) {
    vertice vert = malloc(sizeof(struct vertice));
    vert->nome = malloc((strlen(agnameof(v))+1)*sizeof(char));
    vert->visitado = 0;
    vert->coberto = 0;
    vert->arest_in = constroi_lista();
    vert->arest_out = constroi_lista();
    strcpy(vert->nome, agnameof(v));
    if ( direcionado ){
      guarda_in(g, v, vert->arest_in);
      guarda_out(g, v, vert->arest_out);
    }
    else
      guarda_arestas(g, v, vert->arest_in);
    insere_lista(vert,lista_vertices);
  }
  return lista_vertices;
}

static vertice busca_vertice(char *nome, grafo g){
  vertice v;
  for (no n = primeiro_no(g->vert); n; n = proximo_no(n)){
    v = conteudo(n);
    
    if (!strcmp(v->nome, nome))
      return v;
  }
  return NULL;
}

static void cria_aresta(Agedge_t *a,lista l){
  aresta ar = malloc (sizeof(struct aresta));
  ar->origem = malloc((strlen(agnameof(agtail(a)))+1)*sizeof(char));
  ar->destino = malloc((strlen(agnameof(aghead(a)))+1)*sizeof(char));
  strcpy(ar->origem, agnameof(agtail(a)));  
  strcpy(ar->destino, agnameof(aghead(a)));
  if(agget(a,"peso")) 
    ar->peso = atol(agget(a,"peso"));
  else
    ar->peso = 0;
  ar->coberta = 0;
  insere_lista(ar, l);
}

grafo le_grafo(FILE *input){
  grafo h = malloc(sizeof(struct grafo));
  if(!h)
    return NULL;
  Agraph_t *g = agread(input,NULL);
  h->nome = malloc((strlen(agnameof(g))+1)*sizeof(char));
  strcpy(h->nome, agnameof(g));
  h->direcionado = agisdirected(g);
  h->vert = ajeita_vertices(g,h->direcionado);
  h->n_vertices = (unsigned int)agnnodes(g);
  h->n_arestas =  (unsigned int)agnedges(g);
  if(agget(agfstedge(g, agfstnode(g)),"peso"))
    h->ponderado = 1;
  else
    h->ponderado = 0;

  agclose(g);

  return h;
}

lista vizinhanca(vertice v, int direcao, grafo g){
  lista vz = constroi_lista();

  aresta a;

  if (!direcao){
    for (no n=primeiro_no(v->arest_in); n; n=proximo_no(n)){
      a = conteudo(n);
      if (strcmp(v->nome, a->origem))
	insere_lista(busca_vertice(a->origem, g), vz);
      else
	insere_lista(busca_vertice(a->destino, g), vz);
    }
    return vz;
  }
  if (direcao == -1){ 
    for (no n=primeiro_no(v->arest_in); n; n=proximo_no(n)){
      a = conteudo(n);
      insere_lista(busca_vertice(a->origem, g), vz);
    }
    return vz;
  }
  if (direcao == 1){
    for (no n=primeiro_no(v->arest_out); n; n=proximo_no(n)){
      a = conteudo(n);
      insere_lista(busca_vertice(a->destino, g), vz);
    }
    return vz;
  }
  return NULL;
}

grafo copia_grafo(grafo g){
  grafo tmp;
  vertice t;
  aresta t2;

  tmp = malloc(sizeof(struct grafo));
  tmp->nome = malloc((strlen(g->nome)+1)*sizeof(char));
  strcpy(tmp->nome, g->nome);
  tmp->direcionado = g->direcionado;
  tmp->ponderado = g->ponderado;
  tmp->n_vertices = g->n_vertices;
  tmp->n_arestas = g->n_arestas;
  tmp->vert = constroi_lista();
  for (no n = primeiro_no(g->vert); n; n = proximo_no(n)){
    t = conteudo(n);
    vertice v2 = malloc(sizeof(struct vertice));
    v2->nome = malloc((strlen(t->nome)+1)*sizeof(char));
    strcpy(v2->nome, t->nome);
    v2->arest_in = constroi_lista();
    v2->arest_out = constroi_lista();
    
    for (no n1 = primeiro_no(t->arest_in); n1; n1 = proximo_no(n1)){
      t2 = conteudo(n1);
      aresta a = malloc(sizeof(struct aresta));
      a->origem = malloc((strlen(t2->origem)+1)*sizeof(char));
      a->destino = malloc((strlen(t2->destino)+1)*sizeof(char));
      strcpy(a->origem, t2->origem);
      strcpy(a->destino, t2->destino);
      a->peso = t2->peso;
      insere_lista(a, v2->arest_in);
    }
    if (tmp->direcionado){
      for (no n1 = primeiro_no(t->arest_out); n1; n1 = proximo_no(n1)){
	t2 = conteudo(n1);
	aresta a = malloc(sizeof(struct aresta));
	a->origem = malloc((strlen(t2->origem)+1)*sizeof(char));
	a->destino = malloc((strlen(t2->destino)+1)*sizeof(char));
	strcpy(a->origem, t2->origem);
	strcpy(a->destino, t2->destino);
	a->peso = t2->peso;
	insere_lista(a, v2->arest_out);
      }
    }
    insere_lista(v2, tmp->vert);
  }
  return tmp;
}


unsigned int grau(vertice v, int direcao, grafo g){  
  if(direcao == 1)
    return tamanho_lista(v->arest_out);
  else 
    return tamanho_lista(v->arest_in);
}

int clique(lista l, grafo g){

  if (g->direcionado)
    return 0;
  
  int achou;
  for(no n = primeiro_no(l); n; n = proximo_no(n)){
    lista lt;
    
    lt = vizinhanca(conteudo(n), 0, g);

    for (no n1 = primeiro_no(l); n1; n1 = proximo_no(n1)){
      achou = 0;
      if (!strcmp(nome_vertice(conteudo(n1)), nome_vertice(conteudo(n)))){
	if (!proximo_no(n1))
	  achou = 1;
	else
	  n1 = proximo_no(n1);
      }
      for (no n2 = primeiro_no(lt); n2 && !achou; n2 = proximo_no(n2)){
	if (!strcmp(nome_vertice(conteudo(n2)), nome_vertice(conteudo(n1)))){
	  achou = 1;
	}
	if (!proximo_no(n2) && !achou){
	  destroi_lista(lt, NULL);
	  return 0;
	}
      }
    }
    destroi_lista(lt, NULL);
  }
  return 1;
}

int simplicial(vertice v, grafo g){
  if(clique(vizinhanca(v, 0, g), g))
    return 1;
  else
    return 0;
}

static int acha_aresta(aresta g,lista l){

  aresta a;
  for ( no n=primeiro_no(l); n; n=proximo_no(n)) {
    a = conteudo(n);
    if ( !strcmp(a->destino,g->destino) &&  !strcmp(a->origem,g->origem))
      return 1;
  }

  return 0;
}


static void salva_aresta(vertice v,lista l) {
  aresta a = malloc(sizeof(struct aresta));
  for (no n=primeiro_no(v->arest_in); n; n=proximo_no(n)){
    a = conteudo(n);
    if ( ! acha_aresta(a,l) )
      insere_lista(a,l);
  }
}

grafo escreve_grafo(FILE *output,grafo g){
  if(g){
    if(g->direcionado)
      fprintf(output, "digraph %s {\n",g->nome);
    else
      fprintf(output, "strict graph %s {\n",g->nome);
    vertice v;
    aresta a;
    char traco;
    lista lista_arestas = constroi_lista();
    for(no n = primeiro_no(g->vert);n;n = proximo_no(n)){
      v = conteudo(n);
      //fprintf(output, "   %s\n",v->nome);
      salva_aresta(v,lista_arestas);
    }
    if(g->n_arestas){
      traco = g->direcionado ? '>' : '-';
      for(no n = primeiro_no(lista_arestas);n;n = proximo_no(n)){
        a = conteudo(n);
        long int peso = a -> peso;
        fprintf(output, "   \"%s\" -%c \"%s\"",a->origem,traco,a->destino);
        if(peso)
           fprintf(output, " |peso = %ld|",peso);
        fprintf(output, "\n");
      }
    }
    fprintf(output,"}");
    destroi_lista(lista_arestas, NULL);
    return g;
   }
  return NULL;
}

int cordal(grafo g){
  lista b = busca_largura_lexicografica(g);
  return ordem_perfeita_eliminacao(b, g);
}

static int destroi_aresta(void *ptr) {
    aresta a = ptr;
    if (a) {
      free(a->origem);
      free(a->destino);
      free(a);
      return 1;
    } else {
      return 0;
    }
}

static int destroi_vertice(void *ptr) {
  vertice v = ptr;
  if (v) {
    free(v->nome);
    int i = destroi_lista(v->arest_in, destroi_aresta);
    i &= destroi_lista(v->arest_out, destroi_aresta);
    free(v);
    return i;
  } else {
    return 0;
  }
}

int destroi_grafo(void *g){
  grafo t = g;
  if (t){
    free(t->nome);
    return destroi_lista(t->vert, destroi_vertice);
  }
  return 0;
}

static int remove_vert(char *nome, grafo g){
  for (no n = primeiro_no(g->vert); n; n = proximo_no(n)){
    vertice v = conteudo(n);
    for (no m = primeiro_no(v->arest_in); m; m = proximo_no(m)){
      aresta a = conteudo(m);
      if (!strcmp(a->origem, nome) || !strcmp(a->destino, nome)){
	if (!remove_no(v->arest_in, m, destroi_aresta)){
	  printf("erro ao remover.\n");
	  return 0;
	}
	g->n_arestas--;
      }
    }
  }
  return 1;
}

lista busca_largura_lexicografica(grafo g){
  grafo tmp;
  lista busca = constroi_lista();
  tmp = copia_grafo(g);
  //primeiro vertice do grafo
  vertice v1 = conteudo(primeiro_no(tmp->vert));
  //v1 recebe rotulo N
  v1->rotulo[0] = tmp->n_vertices;
  //vizinhanca v1
  lista viz = vizinhanca(v1, 0, tmp);
  //adiciona v1 a lista busca
  if(!insere_lista(v1, busca))
    printf("Nao conseguiu colocar na lista.\n");
  //remove v1 do grafo
  if(!remove_no(tmp->vert, primeiro_no(tmp->vert), NULL))
    printf("Erro ao remover no.\n");
  tmp->n_vertices--;
  if (!remove_vert(nome_vertice(v1), tmp))
    printf("Erro ao remover.\n");
  //todos vizinhos v1 recebem rotulo N-1
  for (no n = primeiro_no(viz); n; n = proximo_no(n)){
    vertice v2 = conteudo(n);
    v2->rotulo[0] = tmp->n_vertices;
  }
  //enqnto tem vertice no grafo
  while(tmp->n_vertices > 0){
    no m = primeiro_no(tmp->vert);
    vertice maior = conteudo(m);
    for (no n = proximo_no(m); n; n = proximo_no(n)){
      vertice vt = conteudo(n);
      if (maior_rt(vt, maior, 0)){
	maior = vt;
	m = n;
      }
    }
    //vizinhanca maior rotulo
    viz = vizinhanca(maior, 0, tmp);
    //remove maior do grafo
    if(!remove_no(tmp->vert, m, NULL))
      printf("Erro ao remover no.\n");
    tmp->n_vertices--;
    if (!remove_vert(nome_vertice(maior), tmp))
      printf("Erro ao remover.\n");
    //adiciona maior a lista busca
    if(!insere_lista(maior, busca))
      printf("Nao conseguiu colocar na lista.\n");
    for (no n = primeiro_no(viz); n; n = proximo_no(n)){
      vertice v2 = conteudo(n);
      int achou = 0;
      for (int i=0; i<TAMRT && !achou; ++i){
	if (v2->rotulo[i] == 0){
	  v2->rotulo[i] = tmp->n_vertices;
	  achou = 1;
	}
      }
    }
  }
  lista retorno = constroi_lista();
  //devolve lista COM vizinhanca.
  for(no n = primeiro_no(busca); n; n = proximo_no(n)){
    insere_lista(busca_vertice(nome_vertice(conteudo(n)), g), retorno);
  }
  destroi_grafo(tmp);
  destroi_lista(busca, destroi_vertice);
  return retorno;
}

static int maior_rt(vertice v1, vertice v2, int i){
  if (i > TAMRT)
    return 0;
  if (v1->rotulo[i] > v2->rotulo[i])
    return 1;
  else if (v1->rotulo[i] == v2->rotulo[i])
    return maior_rt(v1, v2, ++i);
  return 0;
  /*if (!v1)
    return 0;
  if (!v2)
    return 1;
  if (conteudo(rt1) > conteudo(rt2))
    return 1;
  else if (conteudo(rt1) == conteudo(rt2))
    return maior_rt(proximo_no(rt1), proximo_no(rt2));
  return 0;*/
}

int ordem_perfeita_eliminacao(lista l, grafo g){
  lista viz,viz2;
  vertice v,v1,v2,v4, vd;
  no n,m,o,q;
  int achou;
  printf("Comecando a percorrer lista. t=%d\n\n", tamanho_lista(l));
  //Percorre Busca_lexicografica
  for(n = primeiro_no(l);n;n = proximo_no(n)){
    v = conteudo(n);
    //Pega vizinhança da lista da busca 
    viz = vizinhanca(v,0,g);
    printf("Procurando primeiro vizinho a direita de %s.\n", nome_vertice(v));fflush(stdout);
    //Percorre a vizinhança, se nao for vazia.
    if (tamanho_lista(viz) > 0){
      for(achou = 0, o = proximo_no(n);o && !achou;o = proximo_no(o)){
	v1 = conteudo(o);
	//Olha para elementos a direita da Busca,o = proximo_no(n) me garante que eu compare so com os vizinhos a direita.
	for(m = primeiro_no(viz);m;m = proximo_no(m)){
	  v2 = conteudo(m);
	  //Se for vizinho e esta a direita, achou
	  if (!strcmp(nome_vertice(v1), nome_vertice(v2))){
	    vd = v1;
	    achou = 1;
	  }
	}
      }
    }
    else
      printf("vertice sem vizinho.\n");
    if (achou){
      printf("Achou primeiro vizinho a direita. Eh %s\n", nome_vertice(vd));
      fflush(stdout);
    }
    viz2 = vizinhanca(vd,0,g);
    printf("Tirando os vertices da comparacao das vizinhancas.\n");
    //viz tem que tirar vd, viz2 tem que tirar v
    achou = 0;
    for(no t = primeiro_no(viz); t && !achou; t = proximo_no(t)){
      if (!strcmp(nome_vertice(conteudo(t)), nome_vertice(vd))){
	remove_no(viz, t, NULL);
	achou = 1;
      }
    }
    achou = 0;
    for(no t = primeiro_no(viz2); t && !achou; t = proximo_no(t)){
      if (!strcmp(nome_vertice(conteudo(t)), nome_vertice(v))){
	remove_no(viz2, t, NULL);
	achou = 1;
      }
    }
    
    printf("Comparando vizinhancas.\n");fflush(stdout);

    //tamanho da vizinhanca eh igual, entao percorre, senao nao eh perfeita.
    if (tamanho_lista(viz) == tamanho_lista(viz2)){
      //percorro vizinhanca toda e comparo vertice por vertice.
      for(o = primeiro_no(viz2);o;o = proximo_no(o)){
	achou = 0;
	v2 = conteudo(o);
	for(q = primeiro_no(viz);q && !achou;q = proximo_no(q)){
	  v4 = conteudo(q);
	  if(!strcmp(v2->nome,v4->nome))
	    achou = 1;
	}
	if (!achou){
	  printf("Vizinhancas diferentes.\n");
	  return 0;
	}
      }
    }
    else{
      printf("Vizinhancas de tamanho diferentes.\n");
      return 0;
    }
    printf("Terminou comparacao de vizinhancas.\n\n");fflush(stdout);
  }
  return 1;
}

grafo emparelhamento_maximo(grafo g){
  lista l = constroi_lista();
  while (l = caminho_aumentante(g))
    xor(l, g);
  int i = 0, j = 0;
  for (no n = primeiro_no(g->vert); n; n = proximo_no(n)){
    vertice va = conteudo(n);
    if (va->coberto)
      i++;
    for (no m = primeiro_no(va->arest_in); m; m = proximo_no(m)){
      aresta ar = conteudo(m);
      if (ar->coberta)
	j++;
    }
  }
  printf("acabou caminho aumentante.\n");
  grafo new = malloc(sizeof(struct grafo));
  new->nome = malloc(15*sizeof(char));
  strcpy(new->nome, "Emparelhamento");
  new->direcionado = g->direcionado;
  new->ponderado = g->ponderado;
  new->n_vertices = 0;
  new->n_arestas = 0;
  new->vert = constroi_lista();
  for (no n = primeiro_no(g->vert); n; n = proximo_no(n)){
    vertice aux = conteudo(n);
    if (aux->coberto){
      vertice v1 = malloc(sizeof(struct vertice));
      v1->nome = malloc((strlen(aux->nome)+1)*sizeof(char));
      strcpy(v1->nome, aux->nome);
      v1->coberto = aux->coberto;
      v1->arest_in = constroi_lista();
      v1->arest_out = constroi_lista();
      for (no m = primeiro_no(aux->arest_in); m; m = proximo_no(m)){
	aresta a = conteudo(m);
	if (a->coberta){
	  aresta an = malloc(sizeof(struct aresta));
	  an->origem = malloc((strlen(a->origem)+1)*sizeof(char));
	  an->destino = malloc((strlen(a->destino)+1)*sizeof(char));
	  strcpy(an->origem, a->origem);
	  strcpy(an->destino, a->destino);
	  an->peso = a->peso;
	  an->coberta = a->coberta;
	  insere_lista(an, v1->arest_in);
	  new->n_arestas++;
	}
      }
      insere_lista(v1, new->vert);
      new->n_vertices++;
    }
  }
  return new;
}

void xor(lista l, grafo g){
  for (no n = primeiro_no(l); n; n = proximo_no(n)){
    aresta a = conteudo(n);
    a->coberta = !a->coberta;
    vertice v = busca_vertice(a->origem, g);
    v->coberto = !v->coberto;
    v = busca_vertice(a->destino, g);
    v->coberto = !v->coberto;
  }
}

int busca_caminho(vertice v, lista l, int last, grafo g){
  if (!v->coberto && !v->visitado)
    return 1;
  v->visitado = 1;
  for (no n = primeiro_no(v->arest_in); n; n = proximo_no(n)){
    aresta a = conteudo(n);
    if (a->coberta != last){
      vertice aux;
      if (!strcmp(v->nome, a->origem))
	aux = busca_vertice(a->destino, g);
      else
	aux = busca_vertice(a->origem, g);
      if (!aux->visitado && busca_caminho(aux, l, !last, g)){
	insere_lista(a, l);
	return 1;
      }
    }
  }
  return 0;
}

lista caminho_aumentante(grafo g){
  for (no n = primeiro_no(g->vert); n; n = proximo_no(n)){
    vertice v = conteudo(n);
    if (!v->coberto){
      v->visitado = 1;
      lista l = constroi_lista();
      if (busca_caminho(v, l, 1, g)){
	if (!desvisita_vertices(g)){
	  printf("Erro ao desvisitar vertices.\n");
	  return NULL;
	}
	return l;
      }
      if (!desvisita_vertices(g)){
	printf("Erro ao desvisitar vertices.\n");
	return NULL;
      }
      destroi_lista(l, NULL);
    }
  }
  return NULL;
}

int desvisita_vertices(grafo g){
  for (no n = primeiro_no(g->vert); n; n = proximo_no(n)){
    vertice v = conteudo(n);
    v->visitado = 0;
  }
  return 1;
}
