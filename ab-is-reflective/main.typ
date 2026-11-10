#import "@preview/minimal-note:0.10.1": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#let Grp = math.bold("Grp")
#let Ab = math.bold("Ab")
#let Set = math.bold("Set")
#let Hom = math.op("Hom")
#let subgroup = text[\u{22B4}]

#let infobox(
  body,
  title: none,
  stroke-color: black,
  fill-color: luma(245),
  border-width: 1pt,
  radius: 4pt,
  padding: 8pt,
) = {
  block(
    width: 100%,
    stroke: (paint: stroke-color, thickness: border-width),
    fill: fill-color,
    radius: radius,
    inset: padding,
  )[
    #if title != none [
      *#title*\
    ]
    #body
  ]
}

#let THEOREM_CLR = red
#let LEMMA_CLR = yellow
#let PROP_CLR = green.transparentize(40%)
#let PROOF_CLR = white
#let DEF_CLR = aqua.transparentize(40%)

#let theorem(body) = infobox(
  body,
  title: "Теорема",
  fill-color: THEOREM_CLR
)
#let lemma(body) = infobox(
  body,
  title: "Лемма",
  fill-color: LEMMA_CLR
)
#let prop(body) = infobox(
  body,
  title: "Предложение",
  fill-color: PROP_CLR
)
#let proof(body) = infobox(
  body,
  title: "Доказательство",
  fill-color: PROOF_CLR
)
#let def(body) = infobox(
  body,
  title: "Определение",
  fill-color: DEF_CLR
)

#show: minimal-note.with(
  title: [#math.bold("Ab") --- рефлексивная категория],
  author: [],
  date: [],
  show-outline: false
)

#set text(lang: "ru", font: "New Computer Modern")

Ниже будет показано, что категория абелевых групп является *рефлексивной подкатегорией* в $Grp$.

#def[
  Пусть $cal(C)$ --- категория и $cal(D)$ --- её полная подкатегория.
  Подкатегория $cal(D)$ называется *рефлексивной*, если для функтора вложения $i: cal(D) arrow.hook cal(C)$ существует левый сопряжённый.
]

Тогда задача выглядит так: найти левый сопряжённый для $i: Ab arrow.hook Grp$, т.е. такой функтор $L: Grp -> Ab$, что естественное преобразование
$ Phi: Hom_Ab (L(-), -) ==> Hom_Grp (-, i(-)) $
является естественным изоморфизмом бифункторов $Grp^op times Ab -> Set$.

Несложно догадаться, что довольно очевидный способ сопоставить любой группе $G$ абелеву группы --- это сопоставить ей её абелениазацию $G^"ab"$. Осталось лишь понять, как отображать гомоморфизмы.

Вспомним универсальное свойство факторгруппы.

#def[
  Пусть $G$, $H$ --- группы, $N subgroup G$ --- нормальная подгруппа в $G$.
  Тогда для любого гомоморфизма $f: G -> H$ такого, что $N subset.eq ker f$, существует единственный гомоморфизм $tilde(f): G \/ N -> H$.
  #align(center, diagram({
          node((-1, 0), [$G$])
          node((-1, 2), [$G \/ N$])
          node((1, 0), [$H$])
          edge((-1, 0), (1, 0), [$f$], label-side: left, "->")
          edge((-1, 0), (-1, 2), [$pi$], label-side: right, "->")
          edge((-1, 2), (1, 0), [$tilde(f)$], label-side: right, "-->")
  }))
  Этот гомоморфизм называется *каноническим отображением факторгруппы.*
]

Пусть $phi: G -> H$.
Тогда положим в качестве $f: G -> H^"ab"$ композицию $pi_H compose phi$. Получаем единственный гомоморфизм $tilde(pi_H compose phi) =: phi^"ab"$. При этом квадрат коммутирует:
#align(center, diagram({
	node((-1, 0), [$G$])
	node((-1, 2), [$G^"ab"$])
	node((1, 0), [$H$])
	node((1, 2), [$H^"ab"$])
	edge((-1, 0), (1, 0), [$phi$], label-side: left, "->")
	edge((-1, 0), (-1, 2), [$pi_G$], label-side: right, "->")
	edge((1, 0), (1, 2), [$pi_H$], label-side: left, "->")
	edge((-1, 2), (1, 2), [$phi^"ab"$], label-side: right, "->")
}))
<commutative-square>

#def[
  Определим функтор $(-)^"ab": Grp -> Ab$ следующим образом:
  $ G mapsto G^"ab" :=  G \/ [G,G] $
  $ (f: G -> H) mapsto (f^"ab": G^"ab" -> H^"ab"), $
  где $f^"ab"$ --- каноническое отображение факторгрупп.
]

#prop[
  $(-)^"ab": Grp -> Ab$ --- функтор.
]
// TODO: Написать доказательство
#proof[
  + Пусть $1_G: G -> G, g mapsto g$ --- тождественное отображение.
    Существует единственное отображение, делающее диаграмму коммутативной:
    #align(center, diagram({
            node((-1, 0), [$G$])
            node((-1, 2), [$G^"ab"$])
            node((1, 0), [$G$])
            node((1, 2), [$G^"ab"$])
            edge((-1, 0), (1, 0), [$1_G$], label-side: left, "->")
            edge((-1, 0), (-1, 2), [$pi_G$], label-side: right, "->")
            edge((1, 0), (1, 2), [$pi_G$], label-side: left, "->")
            edge((-1, 2), (1, 2), [$1_G^"ab"$], label-side: right, "->")
    }))
    $ 1_G^"ab" compose pi_G = pi_G compose 1_G $
    $ 1_G^"ab" compose pi_G = pi_G $
    Для $1_G^"ab"$ подходит $1_(G^"ab")$:
    $ 1_(G^"ab") compose pi_G = pi_G $
    В силу единственности, они совпадают.
  + Пусть есть композиция $G ->^f H ->^g K$.
    Существует единственный $(g compose f)^"ab": G^"ab" -> K^"ab"$ такой, что
    $ (g compose f)^"ab" compose pi_G = pi_K compose (g compose f) $

    Домножим композицию $g^"ab" compose f^"ab"$ на $pi_G$:
    $ (g^"ab" compose f^"ab") compose pi_G = g^"ab" compose (f^"ab" compose pi_G) $
    Что равно
    $ g^"ab" compose (pi_H compose f) = (g^"ab" compose pi_H) compose f $
    Что равно
    $ (pi_K compose g) compose f = pi_K  compose (g compose f) $

    Тогда морфизм $g^"ab" compose f^"ab"$ удовлетворяет уравнению. По единственности они совпадают.

    #align(center)[
      Тогда $(-)^"ab": Grp -> Ab$ --- функтор.
  ]
]

#prop[
  Функторы $(-)^"ab"$ и $i$ сопряжены как $(-)^"ab" tack.l i$.
]
#proof[
  По универсальному свойству факторгруппы имеем для каждого $phi: G -> H$, где $G$ --- группа, $H$ --- абелева группа, единственный $phi^"ab": G^"ab" -> H$, что задаёт биекцию на $Hom$-множествах:
  $ Phi^G_H: Hom_Ab (G^"ab", H) -->^~ Hom_Grp (G, H) $
  $ phi^"ab" mapsto phi^"ab" compose pi_G = phi $

  Проверим естественность по $G$. Пусть $f: G_1 -> G_2$. Рассмотрим диаграмму
  #align(center, diagram({
          node((-1, 0), [$Hom_Ab (G_2^"ab", H)$])
          node((-1, 3), [$Hom_Ab (G_1^"ab", H)$])
          node((2, 0), [$Hom_Grp (G_2, H)$])
          node((2, 3), [$Hom_Grp (G_1, H)$])
          edge((-1, 0), (-1, 3), [$(f^"ab")^*$], label-side: right, "->")
          edge((-1, 0), (2, 0), [$Phi^(G_2)_H$], label-side: left, "->")
          edge((-1, 3), (2, 3), [$Phi^(G_1)_H$], label-side: right, "->")
          edge((2, 0), (2, 3), [$f^*$], label-side: left, "->")
  }))
  По часовой стрелке:
  $ phi^"ab" mapsto phi^"ab" compose pi_G_2 mapsto phi^"ab" compose pi_G_2 compose f $
  Против часовой:
  $ phi^"ab" mapsto phi^"ab" compose f^"ab" mapsto phi^"ab" compose f^"ab" compose pi_G_1 $
  По #link(<commutative-square>)[коммутативности квадрата] эти два результата равны.

  Теперь проверим естественность по $H$. Пусть $f: H_1 -> H_2$. Рассмотрим диаграмму:
  #align(center, diagram({
          node((-1, 0), [$Hom_Ab (G^"ab", H_1)$])
          node((-1, 3), [$Hom_Ab (G^"ab", H_2)$])
          node((2, 0), [$Hom_Grp (G, H_1)$])
          node((2, 3), [$Hom_Grp (G, H_2)$])
          edge((-1, 0), (-1, 3), [$f_*$], label-side: right, "->")
          edge((-1, 0), (2, 0), [$Phi^G_(H_1)$], label-side: left, "->")
          edge((-1, 3), (2, 3), [$Phi^G_(H_2)$], label-side: right, "->")
          edge((2, 0), (2, 3), [$f_*$], label-side: left, "->")
  }))

  По часовой:
  $ phi^"ab" mapsto phi^"ab" compose pi_G mapsto f compose phi^"ab" compose pi_G = f compose phi $
  Против часовой:
  $ phi^"ab" mapsto f compose phi^"ab" mapsto f compose phi^"ab" compose pi_G = f compose phi $
  Результаты совпали.

  #align(center)[
    Тогда $(-)^"ab" tack.l i$.
  ]
]
