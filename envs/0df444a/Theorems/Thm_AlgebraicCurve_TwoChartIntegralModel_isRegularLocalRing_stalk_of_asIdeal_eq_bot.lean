-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_stalk_of_asIdeal_eq_bot
-- name    : AlgebraicCurve.TwoChartIntegralModel.isRegularLocalRing_stalk_of_asIdeal_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/4ddd13fd-a168-5a7a-a840-c584cdb2cf25
-- title:
--   Generic-fibre regularity of the two-chart integral model
-- statement:
--   Let $R$ be a commutative Noetherian integral domain, let $K_0$ be a field that is a fraction field of $R$, and let $F$ be a field which is both an $R$-algebra and a $K_0$-algebra, the two structures being compatible through the scalar tower $R \to K_0 \to F$. Let $j \in F$ be an element assumed nonzero (as a `Fact` instance) and transcendental over $R$, and assume that $F$ is finite-dimensional and separable over the intermediate field $K_0(j) =$ `IntermediateField.adjoin K₀ {j}`. Consider the scheme $X =$ [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), defined as the pushout in schemes of the two morphisms `fFin R F j` and `fInf R F j`, namely the morphisms $\operatorname{Spec}$ of the inclusions of the subalgebras `chartAlgFin R F j` $=$ `chartAlg R F {j}` and `chartAlgInf R F j` $=$ `chartAlg R F {j⁻¹}` of $F$ into the ring underlying the middle chart `XMid R F j`; and let `toBase R F j` $: X \to \operatorname{Spec} R$ be the morphism obtained from the two structure maps of $R$ into these subalgebras by the universal property of the pushout. Then for every point $x$ of $X$ whose image under `toBase R F j` is the prime $(0)$ of $R$, i.e. has `asIdeal` equal to $\bot$, the stalk of the structure sheaf of $X$ at $x$ is a regular local ring.
--
--   This is the regularity of the generic fibre of the two-chart integral model: over the generic point of $\operatorname{Spec} R$ the chart rings become Dedekind domains after inverting $R \setminus \{0\}$, so the local rings there are discrete valuation rings or fields. It is one ingredient in the verification, for the two-chart model of the modular curve $X_1(Mp)$, of properness, flatness, regularity and the degeneration data recorded in [`ModularCurve.XOneP.isProper_and_flat_and_isRegularLocalRing_and_twoGluedSmoothCurveDegeneration_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.isProper_and_flat_and_isRegularLocalRing_and_twoGluedSmoothCurveDegeneration_twoChartModel_x1_mul), and it is deduced from the ring-level regularity statements for the localisations of $K_0 \otimes_R$ `chartAlgFin` and $K_0 \otimes_R$ `chartAlgInf` at maximal ideals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_stalk_of_asIdeal_eq_bot.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicCurve.TwoChartIntegralModel.isRegularLocalRing_stalk_of_asIdeal_eq_bot
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))
    (hx : ((AlgebraicCurve.TwoChartIntegralModel.toBase R F j).base x).asIdeal = ⊥) :
    IsRegularLocalRing ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x) := by sorry
