-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_jInvChartInf_mem_and_iotaInf_eq_of_not_mem_range_iotaFin
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_jInvChartInf_mem_and_iotaInf_eq_of_not_mem_range_iotaFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/01bb0464-983a-5ad9-ab86-3d94a120320d
-- title:
--   Points off the finite chart are poles of j
-- statement:
--   Let $R$ be a commutative ring, $F$ a field equipped with an $R$-algebra structure, and $j \in F$ a nonzero element. Write $A_\infty =$ `chartAlgInf R F j` for the $R$-subalgebra of $F$ consisting of those elements of $F$ that are integral over the $R$-subalgebra $R[j^{-1}] =$ `Algebra.adjoin R {j⁻¹}` of $F$, and let `jInvChartInf R F j` be the element $j^{-1}$ of $A_\infty$. Let $X =$ `TwoChartIntegralModel R F j` be the scheme defined as the pushout of the two morphisms `fFin` and `fInf`, obtained by applying `Spec` to the inclusions of the middle chart algebra into the finite and the infinite chart algebras, and let `ιFin`, `ιInf` be the canonical morphisms into this pushout from the spectra of the finite and the infinite chart algebras. The assertion is: for every point $x$ of the underlying topological space of $X$ which does not lie in the image of the continuous map underlying `ιFin`, there exists a prime ideal $\mathfrak q$ of $A_\infty$ such that $j^{-1} \in \mathfrak q$ and the map underlying `ιInf` sends $\mathfrak q$ to $x$.
--
--   This identifies the points of the two-chart integral model lying outside the finite chart: each is the image of a prime of the integral closure of $R[j^{-1}]$ in $F$ at which $j^{-1}$ vanishes, i.e. a point where $j$ has a pole. It is used in the analysis of specialisation and of fibres of the model, and for the Deligne–Rapoport model of $X_0(p)$ it is the step that places all points off the finite chart among the cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_jInvChartInf_mem_and_iotaInf_eq_of_not_mem_range_iotaFin.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
universe u

theorem AlgebraicCurve.TwoChartIntegralModel.exists_jInvChartInf_mem_and_iotaInf_eq_of_not_mem_range_iotaFin
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))
    (hx : x ∉ Set.range (TwoChartIntegralModel.ιFin R F j).base) :
    ∃ 𝔮 : PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgInf R F j),
      TwoChartIntegralModel.jInvChartInf R F j ∈ 𝔮.asIdeal ∧ (TwoChartIntegralModel.ιInf R F j).base 𝔮 = x := by sorry
