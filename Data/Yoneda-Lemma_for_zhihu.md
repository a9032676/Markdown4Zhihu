## 阅读须知
- 本篇文章面向人群是接触过 Category theory (范畴论) 以及 函数式编程，但未曾接触过 Yoneda Lemma (米田引理) 的读者食用。
- 通篇对于范畴论内的专有名词一律采用了英文词汇的形式表达，以防中文翻译各类型文章不统一，可能存在误导性。
- 文章中可能会存在一些 Agda 或 Haskell 语言的代码。没有相关知识不要紧，这只是给予相关领域的朋友一个直觉，用以辅助说明的。
- 这是我在知乎发布的第一篇文章，如对文章本身抱有任何疑问或是纠错欢迎提出，在此感谢各位！

## 前言
[Yoneda Lemma (米田引理)](https://en.wikipedia.org/wiki/Yoneda_lemma) 是范畴论里面一个有关函子的态射实质上可被映射至固定对象上的重要结论，使我们得以透过该引理去推导出更多的定理出来，或者透过该引理观察某些结构上的微妙联系，而对应到计算机编程上亦可擦出火花，比如 Yoneda-embedding 与 CPS 变换 的关系等等。当然，本篇文章主要目的皆指在于引导读者一步步地推导出 Yoneda Lemma，以及给予相应的直觉。

由于 Yoneda Lemma 涉及到一些范畴论上的前置知识，因此在介绍 Yoneda Lemma 之前，首先从 hom-set 开始讲起。

## Hom-set (Hom-集合) 
就函数而言，比方说从  <img src="https://www.zhihu.com/equation?tex=\Bbb{Z}" alt="\Bbb{Z}" class="ee_img tr_noresize" eeimg="1">  到  <img src="https://www.zhihu.com/equation?tex=\Bbb{Z}" alt="\Bbb{Z}" class="ee_img tr_noresize" eeimg="1">  之间的映射存在的可能不止有仅仅一条函数，它可能还存在着很多不同的函数，诸如  <img src="https://www.zhihu.com/equation?tex=f,\ g,\ h, ... : \Bbb{Z} \to \Bbb{Z}" alt="f,\ g,\ h, ... : \Bbb{Z} \to \Bbb{Z}" class="ee_img tr_noresize" eeimg="1">  等等。而由这一束函数所组成的集合，在范畴论中则被称之为 hom-set，即由 morphism(s) 所组成的集合。

由集合作为 object 所组成的 category 则被称之为 category of sets (集合范畴)，它们之间的 morphism(s) 即是 hom-set(s)，因此也可被称为 locally small category (局部小范畴)。

### 定义
给定 object  <img src="https://www.zhihu.com/equation?tex=x,\ y" alt="x,\ y" class="ee_img tr_noresize" eeimg="1">  于 locally small category  <img src="https://www.zhihu.com/equation?tex=C" alt="C" class="ee_img tr_noresize" eeimg="1">  内，hom-set 则是所有从 object  <img src="https://www.zhihu.com/equation?tex=x" alt="x" class="ee_img tr_noresize" eeimg="1">  到  <img src="https://www.zhihu.com/equation?tex=y" alt="y" class="ee_img tr_noresize" eeimg="1">  的 morphisms 所形成的搜集，记为  <img src="https://www.zhihu.com/equation?tex=Hom_C(x,\ y)" alt="Hom_C(x,\ y)" class="ee_img tr_noresize" eeimg="1">  （这里的  <img src="https://www.zhihu.com/equation?tex=C" alt="C" class="ee_img tr_noresize" eeimg="1">  为 category 的名字，或是  <img src="https://www.zhihu.com/equation?tex=C(x,\ y)" alt="C(x,\ y)" class="ee_img tr_noresize" eeimg="1"> ，并且可省略地记为  <img src="https://www.zhihu.com/equation?tex=Hom(x,\ y)" alt="Hom(x,\ y)" class="ee_img tr_noresize" eeimg="1"> ）。

### 例子
设有 category  <img src="https://www.zhihu.com/equation?tex=C" alt="C" class="ee_img tr_noresize" eeimg="1"> ，并且有： <br/>
1. Objects： <img src="https://www.zhihu.com/equation?tex=a,\ b \in obj(C)" alt="a,\ b \in obj(C)" class="ee_img tr_noresize" eeimg="1">  <br/>
2. Morphisms： <img src="https://www.zhihu.com/equation?tex=f : a \to b" alt="f : a \to b" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=g : a \to b" alt="g : a \to b" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=h : a \to b" alt="h : a \to b" class="ee_img tr_noresize" eeimg="1"> 

![](https://raw.githubusercontent.com/a9032676/Markdown4Zhihu/master/Data/Yoneda-Lemma/Yoneda-Lemma-1.png)

## Hom-functor (Hom-函子)

由于 Yoneda Lemma 涉及到 hom-functor 的概念，因此 hom-set 肯定是不足够表达 Yoneda Lemma 含义的，我们还需要事先定义一下何为 hom-functor。而 hom-functor 共分为三种，分别是 covariant，contravariant 以及 mixed-variant hom-functor。

### Covariant Hom-functor (协变 Hom-函子)
我们都知道在 object 之间的 morphism(s) 所组成的集合是 hom-set。而对于 hom-functor 而言，通俗的说即是把 object 从原来的 category 中映射为 hom-set，并且把 morphisms 映射为 hom-sets 之间的 morphisms，进而建立 (covariant) hom-functor 的概念。

那么该如何构造出这一概念？对于这一疑问，我们可以先假设有 locally small category  <img src="https://www.zhihu.com/equation?tex=C" alt="C" class="ee_img tr_noresize" eeimg="1">  以及一些 object，例如  <img src="https://www.zhihu.com/equation?tex=X, A, B \in obj(C)" alt="X, A, B \in obj(C)" class="ee_img tr_noresize" eeimg="1"> ，然后 对于所有  <img src="https://www.zhihu.com/equation?tex=X" alt="X" class="ee_img tr_noresize" eeimg="1">  将作为 fixed object，并且分别有  <img src="https://www.zhihu.com/equation?tex=X" alt="X" class="ee_img tr_noresize" eeimg="1">  到  <img src="https://www.zhihu.com/equation?tex=A" alt="A" class="ee_img tr_noresize" eeimg="1">  以及  <img src="https://www.zhihu.com/equation?tex=X" alt="X" class="ee_img tr_noresize" eeimg="1">  到  <img src="https://www.zhihu.com/equation?tex=B" alt="B" class="ee_img tr_noresize" eeimg="1">  的 hom-sets。那么 (covariant) hom-functor 的样子是这样的：

![](https://raw.githubusercontent.com/a9032676/Markdown4Zhihu/master/Data/Yoneda-Lemma/Yoneda-Lemma-2.png)

从上图可见，当把  <img src="https://www.zhihu.com/equation?tex=X" alt="X" class="ee_img tr_noresize" eeimg="1">  给固定住后，object  <img src="https://www.zhihu.com/equation?tex=A" alt="A" class="ee_img tr_noresize" eeimg="1">  将会映射为一个  <img src="https://www.zhihu.com/equation?tex=Hom(X,\ A)" alt="Hom(X,\ A)" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=B" alt="B" class="ee_img tr_noresize" eeimg="1">  则被映射为  <img src="https://www.zhihu.com/equation?tex=Hom(X,\ B)" alt="Hom(X,\ B)" class="ee_img tr_noresize" eeimg="1"> ，所以说只要把其中一边给固定住了 (这里固定了 hom-set 的左侧，而右侧可变的位置是协变位，因此称为 covariant hom-functor)，对于任何可变的 object (这里则指  <img src="https://www.zhihu.com/equation?tex=A" alt="A" class="ee_img tr_noresize" eeimg="1">  或  <img src="https://www.zhihu.com/equation?tex=B" alt="B" class="ee_img tr_noresize" eeimg="1"> )，便可透过 (covariant) hom-functor 被映射成 hom-set 了。

当然，除了 object 以外，我们还需设想 morphisms 的情况。<br/>
现在设  <img src="https://www.zhihu.com/equation?tex=A" alt="A" class="ee_img tr_noresize" eeimg="1">  和  <img src="https://www.zhihu.com/equation?tex=B" alt="B" class="ee_img tr_noresize" eeimg="1">  之间存在 morphism  <img src="https://www.zhihu.com/equation?tex=f" alt="f" class="ee_img tr_noresize" eeimg="1"> ，那么对于 morphisms 而言，被映射至  <img src="https://www.zhihu.com/equation?tex=Set" alt="Set" class="ee_img tr_noresize" eeimg="1">  之后便是这样：

![](https://raw.githubusercontent.com/a9032676/Markdown4Zhihu/master/Data/Yoneda-Lemma/Yoneda-Lemma-3.png)

即 morphism  <img src="https://www.zhihu.com/equation?tex=f" alt="f" class="ee_img tr_noresize" eeimg="1">  将被映射成  <img src="https://www.zhihu.com/equation?tex=Hom(X,\ f)" alt="Hom(X,\ f)" class="ee_img tr_noresize" eeimg="1">  (这里可以理解为  <img src="https://www.zhihu.com/equation?tex=Hom(id_X,\ f)" alt="Hom(id_X,\ f)" class="ee_img tr_noresize" eeimg="1"> )。

那么便可总结出规律，想要定义出 hom-functor 的概念，必须要知道到底 objects 是应该怎样被映射的，morphisms 亦应怎么被映射的，并且证明其满足 functor laws，最终便可定义出 covariant hom-functor 了。

### 定义
设有 locally small category  <img src="https://www.zhihu.com/equation?tex=C" alt="C" class="ee_img tr_noresize" eeimg="1"> ，固定  <img src="https://www.zhihu.com/equation?tex=C" alt="C" class="ee_img tr_noresize" eeimg="1">  下的 object  <img src="https://www.zhihu.com/equation?tex=X" alt="X" class="ee_img tr_noresize" eeimg="1">  为 fixed object，有：<br/>
1. Objects： <img src="https://www.zhihu.com/equation?tex=A, B \in obj(C)" alt="A, B \in obj(C)" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=Hom(X,\ A)" alt="Hom(X,\ A)" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=Hom(X,\ B) \in obj(Set)" alt="Hom(X,\ B) \in obj(Set)" class="ee_img tr_noresize" eeimg="1"> <br/>
2. Morphisms： <img src="https://www.zhihu.com/equation?tex=f : A \to B, g : X \to A \in mor(C)" alt="f : A \to B, g : X \to A \in mor(C)" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=Hom(X,\ f) \in mor(Set)" alt="Hom(X,\ f) \in mor(Set)" class="ee_img tr_noresize" eeimg="1"> 

则  <img src="https://www.zhihu.com/equation?tex=Hom(X, -) : C \to Set" alt="Hom(X, -) : C \to Set" class="ee_img tr_noresize" eeimg="1">  (或  <img src="https://www.zhihu.com/equation?tex=h_X" alt="h_X" class="ee_img tr_noresize" eeimg="1"> ) 被称为 covariant hom-functor，并有如下图表：

![](https://raw.githubusercontent.com/a9032676/Markdown4Zhihu/master/Data/Yoneda-Lemma/Yoneda-Lemma-4.png)

而 covariant hom-functor 由以下两部分组成：<br/>
 <img src="https://www.zhihu.com/equation?tex=obj(C) \to obj(Set)" alt="obj(C) \to obj(Set)" class="ee_img tr_noresize" eeimg="1"> ： <img src="https://www.zhihu.com/equation?tex=\forall A \in obj(C)，有 A \mapsto Hom(X,\ A)" alt="\forall A \in obj(C)，有 A \mapsto Hom(X,\ A)" class="ee_img tr_noresize" eeimg="1"> <br/>
 <img src="https://www.zhihu.com/equation?tex=mor(C) \to mor(Set)" alt="mor(C) \to mor(Set)" class="ee_img tr_noresize" eeimg="1"> ： <img src="https://www.zhihu.com/equation?tex=\forall f \in A \to B" alt="\forall f \in A \to B" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=g : Hom(X,\ A)" alt="g : Hom(X,\ A)" class="ee_img tr_noresize" eeimg="1"> ，有  <img src="https://www.zhihu.com/equation?tex=g \mapsto f \circ g" alt="g \mapsto f \circ g" class="ee_img tr_noresize" eeimg="1"> 

Covariant hom-functor 本身结构是  <img src="https://www.zhihu.com/equation?tex=F : C \to Set" alt="F : C \to Set" class="ee_img tr_noresize" eeimg="1"> ，因此也可被称为 representable functor (可表函子) 。

### 证明
Identity laws： <img src="https://www.zhihu.com/equation?tex=Hom(X, id_A) = id_A" alt="Hom(X, id_A) = id_A" class="ee_img tr_noresize" eeimg="1"> <br/>
Composition laws： <img src="https://www.zhihu.com/equation?tex=Hom(X,\ g \circ f) = Hom(X,\ g) \circ Hom(X,\ f)" alt="Hom(X,\ g \circ f) = Hom(X,\ g) \circ Hom(X,\ f)" class="ee_img tr_noresize" eeimg="1"> 

由此可见 covariant hom-functor 满足 functor laws，因此它是一个 functor。

### Contravariant Hom-functor (逆变 Hom-函子)
而 contravariant hom-functor，只需把 covariant hom-functor 中 domain (逆变位置) 或 codomain (协变位置) 其中任意一个 category 改为 opposite category，这里我们采用改变逆变位置的 category，即有：

![](https://raw.githubusercontent.com/a9032676/Markdown4Zhihu/master/Data/Yoneda-Lemma/Yoneda-Lemma-5.png)

### 定义
设有 locally small category  <img src="https://www.zhihu.com/equation?tex=C^{op}" alt="C^{op}" class="ee_img tr_noresize" eeimg="1"> ，固定  <img src="https://www.zhihu.com/equation?tex=C" alt="C" class="ee_img tr_noresize" eeimg="1">  下的 object  <img src="https://www.zhihu.com/equation?tex=X" alt="X" class="ee_img tr_noresize" eeimg="1">  为 fixed object，并且有：<br/>
1. Objects： <img src="https://www.zhihu.com/equation?tex=A, B \in Obj(C^{op})" alt="A, B \in Obj(C^{op})" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=Hom(A,\ X), Hom(B,\ X) \in obj(Set)" alt="Hom(A,\ X), Hom(B,\ X) \in obj(Set)" class="ee_img tr_noresize" eeimg="1"> <br/>
2. Morphisms： <img src="https://www.zhihu.com/equation?tex=f : B \to A, g : A \to X \in mor(C)" alt="f : B \to A, g : A \to X \in mor(C)" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=Hom(f,\ X) \in mor(Set)" alt="Hom(f,\ X) \in mor(Set)" class="ee_img tr_noresize" eeimg="1"> <br/>

则  <img src="https://www.zhihu.com/equation?tex=Hom(-, X) : C \to Set" alt="Hom(-, X) : C \to Set" class="ee_img tr_noresize" eeimg="1">  (或  <img src="https://www.zhihu.com/equation?tex=h^X" alt="h^X" class="ee_img tr_noresize" eeimg="1"> ) 被称为 contravariant hom-functor，并有如下图表：

![](https://raw.githubusercontent.com/a9032676/Markdown4Zhihu/master/Data/Yoneda-Lemma/Yoneda-Lemma-6.png)

而 contravariant hom-functor 由以下两部分组成：<br/>
 <img src="https://www.zhihu.com/equation?tex=obj(C^{op}) \to obj(Set)" alt="obj(C^{op}) \to obj(Set)" class="ee_img tr_noresize" eeimg="1"> ： <img src="https://www.zhihu.com/equation?tex=\forall A \in obj(C^{op})" alt="\forall A \in obj(C^{op})" class="ee_img tr_noresize" eeimg="1"> ，有  <img src="https://www.zhihu.com/equation?tex=A \mapsto Hom(A,\ X)" alt="A \mapsto Hom(A,\ X)" class="ee_img tr_noresize" eeimg="1"> <br/>
 <img src="https://www.zhihu.com/equation?tex=mor(C^{op}) \to mor(Set)" alt="mor(C^{op}) \to mor(Set)" class="ee_img tr_noresize" eeimg="1"> ： <img src="https://www.zhihu.com/equation?tex=\forall f \in B \to A" alt="\forall f \in B \to A" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=g : Hom(A,\ X)" alt="g : Hom(A,\ X)" class="ee_img tr_noresize" eeimg="1"> ，有  <img src="https://www.zhihu.com/equation?tex=g \mapsto f \circ g" alt="g \mapsto f \circ g" class="ee_img tr_noresize" eeimg="1"> 

Contravariant hom-functor 本身结构是  <img src="https://www.zhihu.com/equation?tex=F : C^{op} \to Set" alt="F : C^{op} \to Set" class="ee_img tr_noresize" eeimg="1"> ，于拓扑里有另外一个名字，称之为 presheaf (预层) 。

### 证明
Identity laws： <img src="https://www.zhihu.com/equation?tex=Hom(id_A, X) = id_A" alt="Hom(id_A, X) = id_A" class="ee_img tr_noresize" eeimg="1"> <br/>
Composition laws： <img src="https://www.zhihu.com/equation?tex=Hom(g \circ f,\ X) = Hom(g,\ X) \circ Hom(f,\ X)" alt="Hom(g \circ f,\ X) = Hom(g,\ X) \circ Hom(f,\ X)" class="ee_img tr_noresize" eeimg="1"> 

由此可见 contravariant hom-functor 满足 functor laws，因此它是一个 functor。

### Mixed-variant Hom-functor (双变 Hom-函子)
Mixed-variant hom-functor 相较于上述的 covariant 及 contravariant hom-functor，最大的区别是它能同时接受两个变元，即  <img src="https://www.zhihu.com/equation?tex=Hom(-, -) : C^{op} \times C \to Set" alt="Hom(-, -) : C^{op} \times C \to Set" class="ee_img tr_noresize" eeimg="1"> ，因此被称为 mixed-variant hom-functor，该 functor 是一个  <img src="https://www.zhihu.com/equation?tex=Id_C" alt="Id_C" class="ee_img tr_noresize" eeimg="1">  的 profunctor，亦可被视为是一个 bifunctor 的结构。

### 定义
设有 locally small category  <img src="https://www.zhihu.com/equation?tex=C" alt="C" class="ee_img tr_noresize" eeimg="1">  并且有  <img src="https://www.zhihu.com/equation?tex=C" alt="C" class="ee_img tr_noresize" eeimg="1">  的 opposite category  <img src="https://www.zhihu.com/equation?tex=C^{op}" alt="C^{op}" class="ee_img tr_noresize" eeimg="1"> <br/>
Objects： <img src="https://www.zhihu.com/equation?tex=A, A' \in Obj(C^{op})" alt="A, A' \in Obj(C^{op})" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=B, B' \in Obj(C)" alt="B, B' \in Obj(C)" class="ee_img tr_noresize" eeimg="1"> <br/>
Morphisms： <img src="https://www.zhihu.com/equation?tex=f : A' \to A" alt="f : A' \to A" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=h : B \to B'" alt="h : B \to B'" class="ee_img tr_noresize" eeimg="1"> <br/>
Functors： <img src="https://www.zhihu.com/equation?tex=Hom(-, X) : C^{op} \to Set" alt="Hom(-, X) : C^{op} \to Set" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=Hom(X, -) : C \to Set" alt="Hom(X, -) : C \to Set" class="ee_img tr_noresize" eeimg="1"> 

那么即有图：

![](https://raw.githubusercontent.com/a9032676/Markdown4Zhihu/master/Data/Yoneda-Lemma/Yoneda-Lemma-7.png)

而由于  <img src="https://www.zhihu.com/equation?tex=Hom(X, -)" alt="Hom(X, -)" class="ee_img tr_noresize" eeimg="1">  以及  <img src="https://www.zhihu.com/equation?tex=Hom(-, X)" alt="Hom(-, X)" class="ee_img tr_noresize" eeimg="1">  二者皆是从某个 category 中 morphism 至  <img src="https://www.zhihu.com/equation?tex=Set" alt="Set" class="ee_img tr_noresize" eeimg="1"> ，因此该处可构成一 product category (乘积范畴)，即  <img src="https://www.zhihu.com/equation?tex=C^{op} \times C" alt="C^{op} \times C" class="ee_img tr_noresize" eeimg="1"> ，所以有 functor  <img src="https://www.zhihu.com/equation?tex=Hom(-, -) : C^{op} \times C \to Set" alt="Hom(-, -) : C^{op} \times C \to Set" class="ee_img tr_noresize" eeimg="1"> ：

![](https://raw.githubusercontent.com/a9032676/Markdown4Zhihu/master/Data/Yoneda-Lemma/Yoneda-Lemma-8.png)

而对于  <img src="https://www.zhihu.com/equation?tex=Set" alt="Set" class="ee_img tr_noresize" eeimg="1">  中  <img src="https://www.zhihu.com/equation?tex=Hom(f,\ h) : Hom(A,\ B) \to Hom(A',\ B')" alt="Hom(f,\ h) : Hom(A,\ B) \to Hom(A',\ B')" class="ee_img tr_noresize" eeimg="1"> ，假设固定任意一边的变元为  <img src="https://www.zhihu.com/equation?tex=id" alt="id" class="ee_img tr_noresize" eeimg="1"> ，那么 morphisms 则为： <img src="https://www.zhihu.com/equation?tex=Hom(id_A,\ h) : Hom(A, B) \to Hom(A, B')" alt="Hom(id_A,\ h) : Hom(A, B) \to Hom(A, B')" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=Hom(f,\ id_B) : Hom(A,\ B) \to Hom(A',\ B)" alt="Hom(f,\ id_B) : Hom(A,\ B) \to Hom(A',\ B)" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=Hom(id_{A'},\ h) : Hom(A', B) \to Hom(A', B')" alt="Hom(id_{A'},\ h) : Hom(A', B) \to Hom(A', B')" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=Hom(f,\ id_{B'}) : Hom(A,\ B') \to Hom(A',\ B')" alt="Hom(f,\ id_{B'}) : Hom(A,\ B') \to Hom(A',\ B')" class="ee_img tr_noresize" eeimg="1"> ，所以会有图：

![](https://raw.githubusercontent.com/a9032676/Markdown4Zhihu/master/Data/Yoneda-Lemma/Yoneda-Lemma-9.png)

为了证明该图可交换，现在假设有  <img src="https://www.zhihu.com/equation?tex=g \in Hom(A,\ B)" alt="g \in Hom(A,\ B)" class="ee_img tr_noresize" eeimg="1"> ，那么有：

![](https://raw.githubusercontent.com/a9032676/Markdown4Zhihu/master/Data/Yoneda-Lemma/Yoneda-Lemma-10.png)

最终得出结论： <img src="https://www.zhihu.com/equation?tex=g \mapsto h \circ g \circ f : Hom(A,\ B) \to Hom(A',\ B')" alt="g \mapsto h \circ g \circ f : Hom(A,\ B) \to Hom(A',\ B')" class="ee_img tr_noresize" eeimg="1"> ，因此该图可交换。

## Yoneda Lemma
在把上述的 hom-set，hom-functor 等概念定义完毕后，现在我们终于可以开始来谈谈何为 Yoneda Lemma 了，首先我们从它的定义开始。

### 定义
1. 设  <img src="https://www.zhihu.com/equation?tex=C" alt="C" class="ee_img tr_noresize" eeimg="1">  为任意的 locally small category 以及有 category  <img src="https://www.zhihu.com/equation?tex=Set" alt="Set" class="ee_img tr_noresize" eeimg="1"> 
2. 固定某个 object  <img src="https://www.zhihu.com/equation?tex=X \in Obj(C)" alt="X \in Obj(C)" class="ee_img tr_noresize" eeimg="1"> 
3. Functors： <img src="https://www.zhihu.com/equation?tex=Hom(X, -) : C \to Set" alt="Hom(X, -) : C \to Set" class="ee_img tr_noresize" eeimg="1"> ，一个任意的 functor  <img src="https://www.zhihu.com/equation?tex=F : C \to Set" alt="F : C \to Set" class="ee_img tr_noresize" eeimg="1"> 

而 Yoneda Lemma 所描述的即设有任一的对于  <img src="https://www.zhihu.com/equation?tex=Hom(X, -)" alt="Hom(X, -)" class="ee_img tr_noresize" eeimg="1">  与  <img src="https://www.zhihu.com/equation?tex=F" alt="F" class="ee_img tr_noresize" eeimg="1">  之间的 natural transformation (自然变换)  <img src="https://www.zhihu.com/equation?tex=\alpha" alt="\alpha" class="ee_img tr_noresize" eeimg="1"> ，它与  <img src="https://www.zhihu.com/equation?tex=x \in F(X)" alt="x \in F(X)" class="ee_img tr_noresize" eeimg="1">  即可视为是 isomorphic 的。换句话说即对于集合  <img src="https://www.zhihu.com/equation?tex=F(X)" alt="F(X)" class="ee_img tr_noresize" eeimg="1"> ，它必定能够一对一地把 objects 从  <img src="https://www.zhihu.com/equation?tex=F(X)" alt="F(X)" class="ee_img tr_noresize" eeimg="1">  bijection 至  <img src="https://www.zhihu.com/equation?tex=Hom(Hom(X, -),\ F)" alt="Hom(Hom(X, -),\ F)" class="ee_img tr_noresize" eeimg="1">  集合上的 functor。

米田引理的形式化定义如下：


<img src="https://www.zhihu.com/equation?tex=[C,\ Set](Hom(X, -),\ F) \cong F(X) " alt="[C,\ Set](Hom(X, -),\ F) \cong F(X) " class="ee_img tr_noresize" eeimg="1">

其中  <img src="https://www.zhihu.com/equation?tex=[C,\ Set]" alt="[C,\ Set]" class="ee_img tr_noresize" eeimg="1">  是一 functor category (函子范畴)，object 为 functor，morphisms 则为 natural transformations。
有些时候我们也能把 functor category 替换成  <img src="https://www.zhihu.com/equation?tex=Set" alt="Set" class="ee_img tr_noresize" eeimg="1"> ，其含义是一样的，因此有：


<img src="https://www.zhihu.com/equation?tex=Hom(Hom(X, -),\ F) \cong F(X) " alt="Hom(Hom(X, -),\ F) \cong F(X) " class="ee_img tr_noresize" eeimg="1">

### 透过交换图观察米田引理的结构
由于文字叙述往往不是很直观，因此让我们从交换图的角度来观察一下米田引理：

首先定义  <img src="https://www.zhihu.com/equation?tex=A, B \in Obj(C)" alt="A, B \in Obj(C)" class="ee_img tr_noresize" eeimg="1"> ，且有态射  <img src="https://www.zhihu.com/equation?tex=f : A \to B" alt="f : A \to B" class="ee_img tr_noresize" eeimg="1"> ，以及一个任意的 object  <img src="https://www.zhihu.com/equation?tex=X" alt="X" class="ee_img tr_noresize" eeimg="1"> ，因此对于 category  <img src="https://www.zhihu.com/equation?tex=C" alt="C" class="ee_img tr_noresize" eeimg="1"> ，我们有：

![](https://raw.githubusercontent.com/a9032676/Markdown4Zhihu/master/Data/Yoneda-Lemma/Yoneda-Lemma-11.png)

因此对于任意  <img src="https://www.zhihu.com/equation?tex=X" alt="X" class="ee_img tr_noresize" eeimg="1"> ，我们可以定义出 morphism  <img src="https://www.zhihu.com/equation?tex=- : X \to A" alt="- : X \to A" class="ee_img tr_noresize" eeimg="1">  以及  <img src="https://www.zhihu.com/equation?tex=f \circ - : X \to B" alt="f \circ - : X \to B" class="ee_img tr_noresize" eeimg="1"> 。

而后考虑到有 functor  <img src="https://www.zhihu.com/equation?tex=Hom(X,\ -) : C \to Set" alt="Hom(X,\ -) : C \to Set" class="ee_img tr_noresize" eeimg="1">  和  <img src="https://www.zhihu.com/equation?tex=F : C \to Set" alt="F : C \to Set" class="ee_img tr_noresize" eeimg="1"> ，以及有一自然变换  <img src="https://www.zhihu.com/equation?tex=\alpha : Hom(X, -) \to F" alt="\alpha : Hom(X, -) \to F" class="ee_img tr_noresize" eeimg="1"> ，我们能够得出如下图：

![](https://raw.githubusercontent.com/a9032676/Markdown4Zhihu/master/Data/Yoneda-Lemma/Yoneda-Lemma-12.png)

所以在 category  <img src="https://www.zhihu.com/equation?tex=Set" alt="Set" class="ee_img tr_noresize" eeimg="1">  中，有<br/>
Objects： <img src="https://www.zhihu.com/equation?tex=Hom(X,\ A), Hom(X,\ B), F(A), F(B)" alt="Hom(X,\ A), Hom(X,\ B), F(A), F(B)" class="ee_img tr_noresize" eeimg="1"> <br/>
作为 Morphisms 的 Functors： <img src="https://www.zhihu.com/equation?tex=Hom(X,\ f) : Hom(X,\ A) \to Hom(X,\ B)" alt="Hom(X,\ f) : Hom(X,\ A) \to Hom(X,\ B)" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=F\ f : F(A) \to F(B)" alt="F\ f : F(A) \to F(B)" class="ee_img tr_noresize" eeimg="1"> <br/>
作为 Morphisms 的 Natural transformations： <img src="https://www.zhihu.com/equation?tex=\alpha_A : Hom(X,\ A) \to F(A)" alt="\alpha_A : Hom(X,\ A) \to F(A)" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=\alpha_B : Hom(X,\ B) \to F(B)" alt="\alpha_B : Hom(X,\ B) \to F(B)" class="ee_img tr_noresize" eeimg="1"> 。

对于 category  <img src="https://www.zhihu.com/equation?tex=Set" alt="Set" class="ee_img tr_noresize" eeimg="1"> ，由于  <img src="https://www.zhihu.com/equation?tex=(F\ f) \circ \alpha_A = \alpha_B \circ Hom(X,\ f)" alt="(F\ f) \circ \alpha_A = \alpha_B \circ Hom(X,\ f)" class="ee_img tr_noresize" eeimg="1"> ，因此该图可交换。 

### 证明
为了证明米田引理，可以取出  <img src="https://www.zhihu.com/equation?tex=Hom(X,\ A)" alt="Hom(X,\ A)" class="ee_img tr_noresize" eeimg="1">  中的 identity morphism  <img src="https://www.zhihu.com/equation?tex=id_X" alt="id_X" class="ee_img tr_noresize" eeimg="1">  作为实例，即  <img src="https://www.zhihu.com/equation?tex=Hom(X,\ X)" alt="Hom(X,\ X)" class="ee_img tr_noresize" eeimg="1"> ，所以上图将更变为：

![](https://raw.githubusercontent.com/a9032676/Markdown4Zhihu/master/Data/Yoneda-Lemma/Yoneda-Lemma-13.png)

其中包含了  <img src="https://www.zhihu.com/equation?tex=id_X \in Hom(X,\ X)" alt="id_X \in Hom(X,\ X)" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=u \in F(X)" alt="u \in F(X)" class="ee_img tr_noresize" eeimg="1"> ， <img src="https://www.zhihu.com/equation?tex=f \in Hom(X,\ B)" alt="f \in Hom(X,\ B)" class="ee_img tr_noresize" eeimg="1">  以及  <img src="https://www.zhihu.com/equation?tex=\alpha_B\ f \in F(B)" alt="\alpha_B\ f \in F(B)" class="ee_img tr_noresize" eeimg="1"> 。

而现在我们要做的仅仅是证出该图中所有的 natural transformation  <img src="https://www.zhihu.com/equation?tex=\alpha" alt="\alpha" class="ee_img tr_noresize" eeimg="1">  与 functor  <img src="https://www.zhihu.com/equation?tex=F" alt="F" class="ee_img tr_noresize" eeimg="1">  之间是 isomorphic 的，因此需要证明出  <img src="https://www.zhihu.com/equation?tex=toYoneda : \forall X \in C. (\forall \varphi \in C. Hom(X,\ \varphi) \to F(\varphi)) \to F(X)" alt="toYoneda : \forall X \in C. (\forall \varphi \in C. Hom(X,\ \varphi) \to F(\varphi)) \to F(X)" class="ee_img tr_noresize" eeimg="1">  以及  <img src="https://www.zhihu.com/equation?tex=fromYoneda : \forall X \in C. F(X) \to (\forall \varphi \in C. Hom(X,\ \varphi) \to F(\varphi))" alt="fromYoneda : \forall X \in C. F(X) \to (\forall \varphi \in C. Hom(X,\ \varphi) \to F(\varphi))" class="ee_img tr_noresize" eeimg="1">  这两条路是行得通的，所以最终得出证明：<br/>

设  <img src="https://www.zhihu.com/equation?tex=\alpha_\varphi : \forall \varphi. Hom(X,\ \varphi) \to F(\varphi)" alt="\alpha_\varphi : \forall \varphi. Hom(X,\ \varphi) \to F(\varphi)" class="ee_img tr_noresize" eeimg="1"> ：<br/>
 <img src="https://www.zhihu.com/equation?tex=toYoneda" alt="toYoneda" class="ee_img tr_noresize" eeimg="1"> ： <img src="https://www.zhihu.com/equation?tex=id : Hom(\varphi,\ \varphi)" alt="id : Hom(\varphi,\ \varphi)" class="ee_img tr_noresize" eeimg="1"> ，有  <img src="https://www.zhihu.com/equation?tex=\alpha_\varphi\ id = u" alt="\alpha_\varphi\ id = u" class="ee_img tr_noresize" eeimg="1"> <br/>
 <img src="https://www.zhihu.com/equation?tex=fromYoneda" alt="fromYoneda" class="ee_img tr_noresize" eeimg="1"> ： <img src="https://www.zhihu.com/equation?tex=u : F(\varphi)" alt="u : F(\varphi)" class="ee_img tr_noresize" eeimg="1"> ，有  <img src="https://www.zhihu.com/equation?tex=\alpha_\varphi\ f = (F\ f)\ u" alt="\alpha_\varphi\ f = (F\ f)\ u" class="ee_img tr_noresize" eeimg="1"> 

至此证毕。

#### 于 Agda 中的表达
```
toYoneda : (C : Category o m) {X : Obj C} {F : Functor C (𝒮ℯ𝓉 m)}
           → [ C , 𝒮ℯ𝓉 m ]⟨ Hom C [ X ,─] , F ⟩
           → Fₒ F X
toYoneda
  record { id = id }
  record { η = η }
  = η id

fromYoneda : {C : Category o m} {X : Obj C} (F : Functor C (𝒮ℯ𝓉 m))
             → Fₒ F X
             → [ C , 𝒮ℯ𝓉 m ]⟨ Hom C [ X ,─] , F ⟩
fromYoneda
  record { Fₘ = Fₘ }
  u
  = record { η = λ f → (Fₘ f) u }
```

注：该部分只写出了最终的证明步骤，需要查看详尽的前置定义及源码可移步至 [这里](http://home.e7mc.com:12450/9032676/category-research)。

#### 于 Haskell 中表达
```
toYoneda :: (forall a. (x -> a) -> f a) -> f x
toYoneda alpha = alpha id

fromYoneda :: f x -> (forall a. (x -> a) -> f a)
fromYoneda u f = fmap f u
```

注：该证明被直接翻译为 Haskell 中 category theory 的语义，所以与 agda 中把所有在证明过程中所使用的 concept 全部构造出来是有所区别的。

## 结语
至此，Yoneda lemma 证明篇正式完毕，而接下来笔者将会撰写两篇后续的文章，重点讨论 Yoneda embedding (米田嵌入) 与 Continuation passing style (CPS 变换) 的关系，以及 co-Yoneda lemma 的证明。在此感谢各位细心阅览！

## 外部链接
本文部分内容参考或引用至下列网页，也可供作为额外的延伸资源帮助阅读：

- [Yoneda lemma - nLab](https://ncatlab.org/nlab/show/Yoneda+lemma)
- [The Yoneda Lemma - Bartosz Milewski](https://bartoszmilewski.com/2015/09/01/the-yoneda-lemma/)
- [Category Theory II 4.1: Representable Functors](https://www.youtube.com/watch?v=KaBz45nZEZw)
- [Category Theory II 4.2: The Yoneda Lemma](https://www.youtube.com/watch?v=BiWqNdtptDI)