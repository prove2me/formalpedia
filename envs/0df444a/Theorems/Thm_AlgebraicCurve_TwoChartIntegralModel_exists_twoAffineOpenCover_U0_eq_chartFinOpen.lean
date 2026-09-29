-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_twoAffineOpenCover_U0_eq_chartFinOpen
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_twoAffineOpenCover_U0_eq_chartFinOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/98abb990-476f-5be9-8a68-9f7e53a20582
-- title:
--   The two charts form a two-affine open cover with affine overlap
-- statement:
--   Let $R$ be a commutative ring, $F$ a field equipped with an $R$-algebra structure, and $j \in F$ a nonzero element. Let $\mathcal{X} =$ [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) be the scheme obtained as the pushout, in the category of schemes, of the two morphisms `fFin` $\colon$ `XMid` $\to$ `XFin` and `fInf` $\colon$ `XMid` $\to$ `XInf`, each of which is `Spec.map` applied to the corresponding ring inclusion (`inclFin`, respectively `inclInf`) between the affine schemes attached to $(R, F, j)$. Let `chartFinOpen` and `chartInfOpen` be the open subsets of $\mathcal{X}$ given by the ranges of the two pushout inclusions `ιFin` and `ιInf`. The assertion is that there exists a term $\mathcal{V}$ of the structure `Scheme.TwoAffineOpenCover` on $\mathcal{X}$ — that is, a pair of opens $U_0, U_1 \subseteq \mathcal{X}$ together with proofs that $U_0$ is affine, that $U_1$ is affine, that $U_0 \sqcup U_1 = \top$, and that $U_0 \sqcap U_1$ is affine — whose two opens are exactly the two charts: $\mathcal{V}.U_0 =$ `chartFinOpen R F j` and $\mathcal{V}.U_1 =$ `chartInfOpen R F j`.
--
--   This packages the standard two-chart description of the integral model (finite $j$-chart and pole chart, glued over their overlap) into the form required by the two-chart Čech formalism for quasi-coherent cohomology. It is the input for the computations of sections and their base change on integral models of modular curves, being cited by results such as [`ModularCurve.DRModelPackage.bijective_algebraMap_sections_baseChange`](thm.html#ModularCurve.DRModelPackage.bijective_algebraMap_sections_baseChange) and [`ModularCurve.XHDRModelAtP.bijective_algebraMap_sections_baseChange`](thm.html#ModularCurve.XHDRModelAtP.bijective_algebraMap_sections_baseChange).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_twoAffineOpenCover_U0_eq_chartFinOpen.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgebraicCurve.TwoChartIntegralModel.exists_twoAffineOpenCover_U0_eq_chartFinOpen
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    ∃ 𝒱 : (AlgebraicCurve.TwoChartIntegralModel R F j).TwoAffineOpenCover,
      𝒱.U0 = chartFinOpen R F j ∧ 𝒱.U1 = chartInfOpen R F j := by sorry
