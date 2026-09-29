-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_chartAlgFin_inf_chartAlgInf_eq_integralClosure
-- name    : AlgebraicCurve.TwoChartIntegralModel.chartAlgFin_inf_chartAlgInf_eq_integralClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/6fd39232-39ca-5f6b-a6a3-181b7636775d
-- title:
--   Integral over R[j] and over R[j⁻¹] implies integral over R
-- statement:
--   Let $R$ be a commutative ring, let $F$ be a field equipped with an $R$-algebra structure, and let $j$ be an element of $F$, assumed nonzero. For a subset $S \subseteq F$, the $R$-subalgebra `chartAlg R F S` of $F$ consists of those $x \in F$ that are integral over the $R$-subalgebra $R[S] =$ `Algebra.adjoin R S` of $F$; in particular `chartAlgFin R F j` is the set of elements of $F$ integral over $R[j]$ and `chartAlgInf R F j` is the set of elements of $F$ integral over $R[j^{-1}]$, each being the integral closure of the corresponding subalgebra in $F$. The theorem asserts the equality of $R$-subalgebras of $F$
--   $$\bigl(\text{elements integral over } R[j]\bigr) \cap \bigl(\text{elements integral over } R[j^{-1}]\bigr) \;=\; \text{integralClosure } R\, F,$$
--   where the left-hand side is the lattice meet $\sqcap$ of the two subalgebras and the right-hand side is the integral closure of $R$ in $F$. Equivalently: an element of $F$ integral over both $R[j]$ and $R[j^{-1}]$ is integral over $R$, and conversely.
--
--   This is the ring-theoretic computation underlying the global sections of the two-chart integral model [`AlgebraicCurve.TwoChartIntegralModel`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), the pushout of $\operatorname{Spec}$ of the two chart algebras along $\operatorname{Spec}$ of their overlap: the two chart rings, viewed inside $F$, meet exactly in the integral closure of $R$ in $F$. It is used in [`AlgebraicCurve.TwoChartIntegralModel.bijective_algebraMap_globalSections_iff_isIntegrallyClosedIn`](thm.html#AlgebraicCurve.TwoChartIntegralModel.bijective_algebraMap_globalSections_iff_isIntegrallyClosedIn), which characterises when $R \to \Gamma$ is bijective.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_chartAlgFin_inf_chartAlgInf_eq_integralClosure.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicCurve.TwoChartIntegralModel
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgebraicCurve.TwoChartIntegralModel.chartAlgFin_inf_chartAlgInf_eq_integralClosure
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    (chartAlgFin R F j) ⊓ (chartAlgInf R F j) = integralClosure R F := by sorry
