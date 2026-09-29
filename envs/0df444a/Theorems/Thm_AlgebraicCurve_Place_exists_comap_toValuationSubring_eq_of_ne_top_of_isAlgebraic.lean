-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_comap_toValuationSubring_eq_of_ne_top_of_isAlgebraic
-- name    : AlgebraicCurve.Place.exists_comap_toValuationSubring_eq_of_ne_top_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/8c54f91b-4e1b-526c-bdea-c8cf6d7b9f93
-- title:
--   Extension of a valuation subring to a place of E/κ
-- statement:
--   Let $\kappa$, $k$, $E$ be fields with $\kappa$-algebra structures on $k$ and $E$ and a $k$-algebra structure on $E$ forming a scalar tower, with $E$ algebraic over $k$, and let $x \in E$ be such that $E$ is finite-dimensional over the intermediate field $\kappa(x) =$ `IntermediateField.adjoin κ {x}`. Let $W$ be a valuation subring of $k$ which is proper ($W \neq \top$, i.e. $W \neq k$) and which contains the image of $\kappa$, in the sense that $\mathrm{algebraMap}\ \kappa\ k\ (a) \in W$ for every $a : \kappa$. The assertion is that there exists a place $w$ of $E$ over $\kappa$ — that is, a term of [`AlgebraicCurve.Place κ E`](def/AlgebraicCurve_DivisorClassGroup.html#L22), consisting of a valuation subring $\mathcal{O}_w$ of $E$ containing $\mathrm{algebraMap}\ \kappa\ E\ (a)$ for all $a : \kappa$, satisfying $\mathcal{O}_w \neq \top$ and having underlying ring a principal ideal ring — such that the preimage of $\mathcal{O}_w$ under $\mathrm{algebraMap}\ k\ E$ is exactly $W$.
--
--   This is Chevalley's extension theorem for valuation rings, packaged in the form of places of $E$ over the constant field $\kappa$: every proper valuation subring of an intermediate field $k$ containing the constants is the contraction of a place of $E/\kappa$. It is used in the analysis of valuation subrings of the residue fields of Igusa rings at full level, in the descent arguments [`ModularCurve.FullLevel.eq_of_valuationSubring_residueField_igusaRing_of_floorTrace_descent`](thm.html#ModularCurve.FullLevel.eq_of_valuationSubring_residueField_igusaRing_of_floorTrace_descent) and its variants for the values two and three.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_comap_toValuationSubring_eq_of_ne_top_of_isAlgebraic.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_comap_toValuationSubring_eq_of_ne_top_of_isAlgebraic
    {κ : Type*} [Field κ] {k : Type*} [Field k] {E : Type*} [Field E]
    [Algebra κ k] [Algebra k E] [Algebra κ E] [IsScalarTower κ k E] [Algebra.IsAlgebraic k E]
    (x : E) [FiniteDimensional ↥(IntermediateField.adjoin κ ({x} : Set E)) E]
    (W : ValuationSubring k) (hW : W ≠ ⊤) (hκ : ∀ a : κ, algebraMap κ k a ∈ W) :
    ∃ w : AlgebraicCurve.Place κ E, w.toValuationSubring.comap (algebraMap k E) = W := by sorry
