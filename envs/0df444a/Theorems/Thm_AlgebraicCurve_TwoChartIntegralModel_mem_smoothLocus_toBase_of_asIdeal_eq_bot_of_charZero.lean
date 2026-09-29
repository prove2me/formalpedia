-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_smoothLocus_toBase_of_asIdeal_eq_bot_of_charZero
-- name    : AlgebraicCurve.TwoChartIntegralModel.mem_smoothLocus_toBase_of_asIdeal_eq_bot_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/772aa376-0689-5a00-8fa3-4f6f1c375acd
-- title:
--   Points over the generic point lie in the smooth locus
-- statement:
--   Let $R$ be a discrete valuation domain, let $K_0$ be a field of characteristic zero realised as a fraction field of $R$, and let $F$ be a field that is an algebra over both $R$ and $K_0$ compatibly with $R \to K_0$. Let $j \in F$ be nonzero and transcendental over $R$, and assume $F$ is finite-dimensional and separable over the intermediate field $K_0(j) =$ `IntermediateField.adjoin K₀ {j}`. Let $\mathfrak{X} =$ [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) be the scheme obtained as the pushout in `Scheme` of the two morphisms `fFin` and `fInf`, the spectra of the inclusions `inclFin`, `inclInf` of the chart algebras `chartAlgFin R F j` $=$ `chartAlg R F {j}` and `chartAlgInf R F j` $=$ `chartAlg R F {j⁻¹}` (subalgebras of $F$ over $R$) into the middle algebra, and let `toBase R F j : 𝔛 ⟶ Spec R` be the morphism induced by the $R$-algebra structures on the two chart algebras; assume this morphism is locally of finite presentation. Then every point $y$ of $\mathfrak{X}$ whose image prime in $\operatorname{Spec} R$ has underlying ideal $\bot$, i.e. every point over the generic point of $\operatorname{Spec} R$, lies in the smooth locus of `toBase R F j`.
--
--   This is the statement that the generic fibre of the two-chart integral model of the $j$-line in $F$ over a characteristic-zero discrete valuation ring is contained in the smooth locus of the structure morphism. It feeds the construction of normal proper models of curves over valuation subrings with prescribed generic fibre, used downstream in [`AlgebraicGeometry.exists_normalProperModel_of_valuationSubrings_of_form_of_isAlgebraic_relDimOne_genComplete_henselian`](thm.html#AlgebraicGeometry.exists_normalProperModel_of_valuationSubrings_of_form_of_isAlgebraic_relDimOne_genComplete_henselian).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_mem_smoothLocus_toBase_of_asIdeal_eq_bot_of_charZero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.mem_smoothLocus_toBase_of_asIdeal_eq_bot_of_charZero
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type u) [Field K₀] [CharZero K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    [LocallyOfFinitePresentation (toBase R F j)]
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) (hy : ((toBase R F j).base y).asIdeal = ⊥) :
    y ∈ (toBase R F j).smoothLocus := by sorry
