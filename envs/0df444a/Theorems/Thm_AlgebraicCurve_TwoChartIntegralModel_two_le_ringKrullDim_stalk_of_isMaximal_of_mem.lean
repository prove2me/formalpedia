-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_two_le_ringKrullDim_stalk_of_isMaximal_of_mem
-- name    : AlgebraicCurve.TwoChartIntegralModel.two_le_ringKrullDim_stalk_of_isMaximal_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/9b29a1ee-4474-527a-8413-b7333077a12d
-- title:
--   Krull dimension ≥ 2 at closed special-fibre points of the finite chart
-- statement:
--   Let $A$ be a discrete valuation ring (a commutative domain that is a discrete valuation ring), let $F$ be a field equipped with an $A$-algebra structure, and let $j \in F$ be non-zero and transcendental over $A$, i.e. the evaluation map $A[X] \to F$ at $j$ is injective. Let $\varpi \in A$ be such that the maximal ideal of $A$ equals $\operatorname{span}\{\varpi\}$. Write $B =$ `chartAlgFin A F j` for the $A$-subalgebra of $F$ consisting of those elements of $F$ that are integral over $A[j] =$ `Algebra.adjoin A {j}`, so that the finite chart is $X_{\mathrm{fin}} = \operatorname{Spec} B$, and let `TwoChartIntegralModel A F j` be the scheme obtained as the pushout of the two morphisms `fFin A F j` and `fInf A F j` out of the middle chart. Let $y$ be a point of $X_{\mathrm{fin}}$, that is a prime ideal of $B$, assume that $y$ is a maximal ideal of $B$, and assume that the image of $\varpi$ under $A \to B$ lies in $y$. Then the Krull dimension of the stalk of the structure sheaf of `TwoChartIntegralModel A F j` at the image of $y$ under the base map of the chart morphism `ιFin A F j` is at least $2$ (an inequality in `WithBot ℕ∞`).
--
--   This is the statement that an integral model of a curve over a discrete valuation ring has local rings of dimension at least two at closed points of the special fibre lying in the $j$-finite chart; the exact value two is not asserted. It is used in the comparison of closed points of the special fibre with places of the function field, and in the construction of integral models of modular curves over discretely valued bases, where the closed points in question are the supersingular ones.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_two_le_ringKrullDim_stalk_of_isMaximal_of_mem.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.two_le_ringKrullDim_stalk_of_isMaximal_of_mem
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (F : Type u) [Field F] [Algebra A F] (j : F) [Fact (j ≠ 0)]
    (htj : Transcendental A j)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (y : ↥(XFin A F j)) (hymax : y.asIdeal.IsMaximal)
    (hyϖ : algebraMap A ↥(chartAlgFin A F j) ϖ ∈ y.asIdeal) :
    2 ≤ ringKrullDim ↑((AlgebraicCurve.TwoChartIntegralModel A F j).presheaf.stalk ((ιFin A F j).base y)) := by sorry
