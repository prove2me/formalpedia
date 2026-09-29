-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isFinite_and_finrank_subschemeIota_comp_eq_of_map_germ_eq_maximalIdeal
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.isFinite_and_finrank_subschemeIota_comp_eq_of_map_germ_eq_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/c3215349-9b86-592e-b8bd-9240d2b1943b
-- title:
--   Finite of rank N over k: reduced k-rational support
-- statement:
--   Let $k$ be a field, let $X$ be a scheme equipped with a morphism $q : X \to \operatorname{Spec} k$ (no finiteness, separatedness or flatness of $q$ is assumed), and let $K$ be a quasi-coherent ideal sheaf datum on $X$, with associated closed immersion `K.subschemeι` of the closed subscheme cut out by $K$. Suppose given $N : \mathbb{N}$ and an injective family $x : \operatorname{Fin} N \to X$ of points such that: the support of $K$, as a subset of $X$, is exactly the set $\{x_0,\dots,x_{N-1}\}$; for each $i$ there is an affine open $U \subseteq X$ containing $x_i$ such that the ideal $K(U)$ of $\mathcal{O}_X(U)$ maps, under the germ homomorphism $\mathcal{O}_X(U) \to \mathcal{O}_{X,x_i}$, onto an ideal generating the maximal ideal of the local ring $\mathcal{O}_{X,x_i}$; and for each $i$ the point $x_i$ is $k$-rational in the sense that there is a section $s : \operatorname{Spec} k \to X$ of $q$ (i.e. $s$ followed by $q$ is the identity) whose image on underlying spaces contains $x_i$. The conclusion is that the composite of `K.subschemeι` with $q$ is a finite morphism of schemes, and that its `finrank` at every point $t$ of $\operatorname{Spec} k$ equals $N$.
--
--   This is the basic computation that a closed subscheme supported on $N$ distinct $k$-rational points, reduced at each of them, is finite of degree $N$ over $\operatorname{Spec} k$; the hypothesis that the stalk of the ideal is the full maximal ideal is what forces each point to contribute $1$ rather than a higher multiplicity. It is used to count intersection or divisor degrees on models of modular curves, being invoked in the computation of degrees of subschemes cut out by ideals on Deligne–Rapoport type models and in a criterion for invertibility of a comap kernel with rank one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_isFinite_and_finrank_subschemeIota_comp_eq_of_map_germ_eq_maximalIdeal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.isFinite_and_finrank_subschemeIota_comp_eq_of_map_germ_eq_maximalIdeal
    {k : Type u} [Field k] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k))
    (K : X.IdealSheafData) {N : ℕ} (x : Fin N → X) (hx : Function.Injective x)
    (hsupp : (K.support : Set X) = Set.range x)
    (hmax : ∀ i, ∃ (U : X.affineOpens) (hU : x i ∈ (U : X.Opens)),
      Ideal.map (X.presheaf.germ (U : X.Opens) (x i) hU).hom (K.ideal U) = IsLocalRing.maximalIdeal (X.presheaf.stalk (x i)))
    (hrat : ∀ i, ∃ s : Spec (CommRingCat.of k) ⟶ X, s ≫ q = 𝟙 _ ∧ x i ∈ Set.range s.base) :
    IsFinite (K.subschemeι ≫ q) ∧ ∀ t : Spec (CommRingCat.of k), (K.subschemeι ≫ q).finrank t = N := by sorry
