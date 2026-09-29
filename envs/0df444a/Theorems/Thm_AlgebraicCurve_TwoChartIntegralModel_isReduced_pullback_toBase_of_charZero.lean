-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_charZero
-- name    : AlgebraicCurve.TwoChartIntegralModel.isReduced_pullback_toBase_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/6413cc01-f1e0-5cd1-abe1-5f4a9b034cf3
-- title:
--   Characteristic-zero fibres of the two-chart model are reduced
-- statement:
--   Let $R$ be a commutative domain, and let $K_0$ be a field which is an $R$-algebra realising $K_0$ as the fraction field of $R$ (`IsFractionRing R K₀`) and which has characteristic $0$. Let $F$ be a field that is both an $R$-algebra and a $K_0$-algebra, the two structures being compatible via the scalar tower $R \to K_0 \to F$, and let $j \in F$ be nonzero. Let $k$ be a further field that is an $R$-algebra and a $K_0$-algebra, again compatibly, so that the induced morphism $\operatorname{Spec} k \to \operatorname{Spec} R$ factors through the generic point $\operatorname{Spec} K_0$. Write $X =$ [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) for the scheme obtained as the pushout, in schemes, of the two morphisms $\operatorname{Spec}$ applied to the inclusions of the $R$-subalgebras `chartAlg R F {j}` and `chartAlg R F {j⁻¹}` of $F$ into the middle ring, and $\mathrm{toBase}$ for the morphism $X \to \operatorname{Spec} R$ obtained from the structure maps $R \to$ `chartAlg R F {j}` and $R \to$ `chartAlg R F {j⁻¹}` by the universal property of the pushout. The assertion is that the fibre product of $\mathrm{toBase}$ with $\operatorname{Spec} k \to \operatorname{Spec} R$, i.e. the base change $X \times_{\operatorname{Spec} R} \operatorname{Spec} k$, is a reduced scheme.
--
--   This is the reducedness half of generic smoothness/reducedness statements for the fibres of the two-chart integral model: over a residue field of characteristic zero reached through the fraction field of the base, the fibre acquires no nilpotents. It is used in the study of the model of the modular curve $X_1(p)$, being cited by [`ModularCurve.XOneP.isReduced_pullback_modelTo_of_isAlgClosed_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.isReduced_pullback_modelTo_of_isAlgClosed_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_charZero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicCurve.TwoChartIntegralModel.isReduced_pullback_toBase_of_charZero
    (R : Type u) [CommRing R] [IsDomain R] (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀] [CharZero K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F] (j : F) [Fact (j ≠ 0)]
    (k : Type u) [Field k] [Algebra R k] [Algebra K₀ k] [IsScalarTower R K₀ k] :
    AlgebraicGeometry.IsReduced
      (pullback (AlgebraicCurve.TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R k)))) := by sorry
