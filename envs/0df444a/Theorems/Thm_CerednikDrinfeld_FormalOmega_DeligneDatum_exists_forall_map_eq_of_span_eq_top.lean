-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_forall_map_eq_of_span_eq_top
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.exists_forall_map_eq_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/57a8df21-eeea-54ef-8f08-3486f0957926
-- title:
--   Zariski gluing of Deligne data over a finite cover
-- statement:
--   Fix a commutative ring $\mathcal O$, a field $K$ that is an $\mathcal O$-algebra, an element $\pi \in \mathcal O$, and a commutative $\mathcal O$-algebra $B$. Let $f_1,\dots,f_n \in B$ generate the unit ideal, let $L_i$ be commutative rings that are simultaneously $B$- and $\mathcal O$-algebras, compatibly, and realise the localisation of $B$ away from $f_i$, and let $L_{ij}$ be likewise $\mathcal O$-compatible $B$-algebras realising the localisation away from $f_i f_j$; let $l_{ij} : L_i \to L_{ij}$ and $r_{ij} : L_j \to L_{ij}$ be $\mathcal O$-algebra maps commuting with the structure maps from $B$. Suppose given, for each $i$, a Deligne datum $x_i$ over $L_i$ for $\pi$: an assignment to every full lattice $M \subset K^2$ of a submodule $\mathrm{line}\,M$ of $L_i \otimes_{\mathcal O} M$ with invertible quotient, monotone under lattice inclusions, equivariant for scalar homotheties, and satisfying Deligne's non-degeneracy condition at every prime of $L_i$. Assume the base changes of $x_i$ along $l_{ij}$ and of $x_j$ along $r_{ij}$ (lines being replaced by the spans of their images) agree for all $i,j$. Then there is a Deligne datum $d$ over $B$ whose base change along each structure map $B \to L_i$ equals $x_i$.
--
--   This is the gluing (existence) half of the assertion that Drinfeld's formal upper half plane functor $\widehat\Omega$ is a sheaf for the Zariski topology on affine schemes, stated for a finite cover by basic opens $\operatorname{Spec} B[1/f_i]$. It is combined with the corresponding uniqueness statement in [`CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_forall_map_eq_and_exists_forall_map_eq_of_span_eq_top`](thm.html#CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_forall_map_eq_and_exists_forall_map_eq_of_span_eq_top), and is used in verifying the lifting property for the fine moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_forall_map_eq_of_span_eq_top.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_forall_map_eq_of_span_eq_top
    (𝒪 : Type) [CommRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] (π : 𝒪)
    (B : Type) [CommRing B] [Algebra 𝒪 B]
    (n : ℕ) (f : Fin n → B) (hf : Ideal.span (Set.range f) = ⊤)
    (L : Fin n → Type) [∀ i, CommRing (L i)] [∀ i, Algebra B (L i)] [∀ i, Algebra 𝒪 (L i)]
    [∀ i, IsScalarTower 𝒪 B (L i)] [∀ i, IsLocalization.Away (f i) (L i)]
    (L₂ : Fin n → Fin n → Type) [∀ i j, CommRing (L₂ i j)] [∀ i j, Algebra B (L₂ i j)] [∀ i j, Algebra 𝒪 (L₂ i j)]
    [∀ i j, IsScalarTower 𝒪 B (L₂ i j)] [∀ i j, IsLocalization.Away (f i * f j) (L₂ i j)]
    (l : ∀ i j, L i →ₐ[𝒪] L₂ i j) (r : ∀ i j, L j →ₐ[𝒪] L₂ i j)
    (hl : ∀ i j (b : B), l i j (algebraMap B (L i) b) = algebraMap B (L₂ i j) b)
    (hr : ∀ i j (b : B), r i j (algebraMap B (L j) b) = algebraMap B (L₂ i j) b)
    (x : ∀ i, OmegaObj (K := K) π (L i))
    (hx : ∀ i j, DeligneDatum.map π (l i j) (x i) = DeligneDatum.map π (r i j) (x j)) :
    ∃ d : OmegaObj (K := K) π B, ∀ i, DeligneDatum.map π (IsScalarTower.toAlgHom 𝒪 B (L i)) d = x i := by sorry
