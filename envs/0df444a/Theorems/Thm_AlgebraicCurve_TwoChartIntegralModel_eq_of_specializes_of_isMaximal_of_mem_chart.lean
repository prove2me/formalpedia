-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_eq_of_specializes_of_isMaximal_of_mem_chart
-- name    : AlgebraicCurve.TwoChartIntegralModel.eq_of_specializes_of_isMaximal_of_mem_chart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/b5ec3dac-7f77-5603-959b-9be6990fff1e
-- title:
--   Maximal chart points over varpi are closed in the model
-- statement:
--   Let $R$ be a discrete valuation domain with $\varpi \in R$ generating its maximal ideal, let $K_0$ be a fraction field of $R$, and let $F$ be a field that is both an $R$-algebra and a $K_0$-algebra compatibly. Let $j \in F$ be nonzero and transcendental over $R$, and assume $F$ is finite-dimensional and separable over the intermediate field $K_0(j)$. Write $A_{\mathrm{fin}}$ for `chartAlgFin R F j`, the subalgebra of elements of $F$ integral over $R[j] =$ `Algebra.adjoin R {j}`, and $A_\infty$ for `chartAlgInf R F j`, the elements of $F$ integral over $R[j^{-1}]$; the model `TwoChartIntegralModel R F j` is the pushout of the two morphisms $\mathrm{XMid} \to \operatorname{Spec} A_{\mathrm{fin}}$ and $\mathrm{XMid} \to \operatorname{Spec} A_\infty$, with $\iota_{\mathrm{fin}}$, $\iota_\infty$ the canonical morphisms from the two charts. Let $x$ be a point of this model which is the image under $\iota_{\mathrm{fin}}$ of a prime of $A_{\mathrm{fin}}$, or under $\iota_\infty$ of a prime of $A_\infty$, that is maximal and contains the image of $\varpi$. Then every point $z$ of the model to which $x$ specialises equals $x$; that is, $x$ is a closed point.
--
--   This identifies the points of the special fibre lying at maximal primes of one of the two affine charts as closed points of the glued integral model, the statement being phrased as the specialisation-order assertion that such a point specialises only to itself. It is used in the construction of normal proper models of curves over a discrete valuation ring and in the identification of centres on the integral models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_eq_of_specializes_of_isMaximal_of_mem_chart.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.eq_of_specializes_of_isMaximal_of_mem_chart
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))

    (hx : (∃ y : ↥(XFin R F j), (ιFin R F j).base y = x ∧ y.asIdeal.IsMaximal ∧
        algebraMap R ↥(chartAlgFin R F j) ϖ ∈ y.asIdeal) ∨
      (∃ y : ↥(XInf R F j), (ιInf R F j).base y = x ∧ y.asIdeal.IsMaximal ∧
        algebraMap R ↥(chartAlgInf R F j) ϖ ∈ y.asIdeal))
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) (hz : x ⤳ z) :
    z = x := by sorry
