-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_forall_map_eq_of_span_eq_top
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_forall_map_eq_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/caf5163c-9cb6-56dd-8020-c832d57ba2cd
-- title:
--   Deligne data are determined on a finite Zariski cover
-- statement:
--   Let $\mathcal{O}$ be a commutative ring, $K$ a field equipped with an $\mathcal{O}$-algebra structure, $\pi \in \mathcal{O}$, and $B$ a commutative $\mathcal{O}$-algebra. Let $n \in \mathbb{N}$ and $f : \mathrm{Fin}\,n \to B$ be elements generating the unit ideal of $B$, and for each $i$ let $L_i$ be a commutative ring which is both a $B$-algebra and an $\mathcal{O}$-algebra, compatibly as a scalar tower over $\mathcal{O}$, and which is a localisation of $B$ away from $f_i$. Let $d, d'$ be two elements of `OmegaObj` $\pi$ $B$, that is, two Deligne data over $B$: each assigns to every full lattice $M \subset K^2$ a $B$-submodule `line` $M$ of $B \otimes_{\mathcal{O}} M$ whose quotient is an invertible $B$-module, subject to monotonicity along inclusions of lattices, equivariance under the homothety matrices `scalarGL` $c$ for $c \in K^\times$, and the nondegeneracy condition which, for every prime ideal $\mathfrak{p}$ of $B$, requires lattices $M' \subseteq M$ with $\pi M \subseteq M'$ such that elements of $M$ outside $M'$, and elements of $M'$ not divisible by $\pi$ in $M$, have their images avoiding the line plus $\mathfrak{p}$-torsion part. If for every $i$ the base changes `DeligneDatum.map` of $d$ and of $d'$ along the structure map $B \to L_i$ coincide, then $d = d'$.
--
--   This is the separation (injectivity) half of the assertion that Drinfeld's formal upper half plane functor $\widehat{\Omega}$, described by Deligne data of lines in base-changed lattices, is a Zariski sheaf on affine schemes. It is used in the combined sheaf statement and in the verification of the fine moduli properties of the associated quaternionic moduli problem, specifically in the existence and uniqueness of lifts along square-zero extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_forall_map_eq_of_span_eq_top.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_forall_map_eq_of_span_eq_top
    (𝒪 : Type) [CommRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] (π : 𝒪)
    (B : Type) [CommRing B] [Algebra 𝒪 B]
    (n : ℕ) (f : Fin n → B) (hf : Ideal.span (Set.range f) = ⊤)
    (L : Fin n → Type) [∀ i, CommRing (L i)] [∀ i, Algebra B (L i)] [∀ i, Algebra 𝒪 (L i)]
    [∀ i, IsScalarTower 𝒪 B (L i)] [∀ i, IsLocalization.Away (f i) (L i)]
    (d d' : OmegaObj (K := K) π B)
    (h : ∀ i, DeligneDatum.map π (IsScalarTower.toAlgHom 𝒪 B (L i)) d =
      DeligneDatum.map π (IsScalarTower.toAlgHom 𝒪 B (L i)) d') : d = d' := by sorry
