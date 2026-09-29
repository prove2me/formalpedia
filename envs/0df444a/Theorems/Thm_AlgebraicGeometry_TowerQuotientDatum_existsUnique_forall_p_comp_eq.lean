-- Prove2me | Theorems.Thm_AlgebraicGeometry_TowerQuotientDatum_existsUnique_forall_p_comp_eq
-- name    : AlgebraicGeometry.TowerQuotientDatum.existsUnique_forall_p_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/9b521409-4eb1-5dc6-8116-0ee60af820de
-- title:
--   Global universal property of a tower quotient datum
-- statement:
--   Let $\mathcal{O}$ be a commutative ring and $\pi \in \mathcal{O}$, let $X : \mathbb{N} \to \mathrm{Scheme}$ be a family of schemes equipped with structure morphisms $xb_n : X_n \to \operatorname{Spec}(\mathcal{O}/(\pi^{n+1}))$ and transition morphisms $xt_n : X_n \to X_{n+1}$, and let $G$ be a group acting on each level through monoid homomorphisms $a_n : G \to \operatorname{Aut}(X_n)$. Let $D$ be a `TowerQuotientDatum` for these data, that is: schemes $Y_n$ with structure morphisms $yb_n : Y_n \to \operatorname{Spec}(\mathcal{O}/(\pi^{n+1}))$ and transitions $yt_n : Y_n \to Y_{n+1}$ making each square $(yt_n, yb_n, yb_{n+1})$ a pullback of $\operatorname{Spec}$ of the quotient map $\mathcal{O}/(\pi^{n+2}) \to \mathcal{O}/(\pi^{n+1})$, with every $yb_n$ proper and flat; morphisms $p_n : X_n \to Y_n$ over the base ($p_n$ followed by $yb_n$ equals $xb_n$), commuting with the transitions and making the square $(xt_n, p_n, p_{n+1}, yt_n)$ a pullback, invariant under $G$ (i.e. $(a_n g)$ followed by $p_n$ equals $p_n$), finite, surjective, with $p_n$ restricted over every open of $Y_n$ an epimorphism; together with the field `univ_loc`, a universal property of the same shape for families of opens $U_n \subseteq Y_n$ satisfying $(yt_n)^{-1}(U_{n+1}) = U_n$. Let $T$ be a scheme and $w_n : X_n \to T$ morphisms that are $G$-invariant, $(a_n g)$ followed by $w_n$ equals $w_n$ for all $n$ and $g$, and compatible with the transitions, $xt_n$ followed by $w_{n+1}$ equals $w_n$. Then there is a unique family of morphisms $u_n : Y_n \to T$ such that $p_n$ followed by $u_n$ equals $w_n$ for every $n$.
--
--   This is the global form of the universal property of the quotient $p_n : X_n \to Y_n$ of a tower by a finite group action: $G$-invariant morphisms out of the tower factor uniquely through the quotient tower. It is used to obtain the universal property of the descended Čerednik–Drinfeld quotient, in [`CerednikDrinfeld.FormalOmega.descendedQuotientMap_univ`](thm.html#CerednikDrinfeld.FormalOmega.descendedQuotientMap_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TowerQuotientDatum_existsUnique_forall_p_comp_eq.lean

import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.TowerQuotientDatum.existsUnique_forall_p_comp_eq
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G : Type) [Group G] (a : ∀ n : ℕ, G →* Aut (X n))
    (D : TowerQuotientDatum 𝒪 π X xb xt G a)
    (T : Scheme.{0}) (w : ∀ n : ℕ, X n ⟶ T)
    (hinv : ∀ (n : ℕ) (g : G), (a n g).hom ≫ w n = w n)
    (hxt : ∀ n : ℕ, xt n ≫ w (n + 1) = w n) :
    ∃! u : ∀ n : ℕ, D.Y n ⟶ T, ∀ n : ℕ, D.p n ≫ u n = w n := by sorry
