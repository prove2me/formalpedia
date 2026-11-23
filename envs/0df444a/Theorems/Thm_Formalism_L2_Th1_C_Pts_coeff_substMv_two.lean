-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Pts_coeff_substMv_two
-- name    : Formalism.L2.Th1.C.Pts.coeff_substMv_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:23:45.171472+00:00
-- url     : https://prove2.me/theorems/87b0f62a-f3b9-45ac-8728-11b12c635a94
-- title:
--   Pts: coeff subst Mv two
-- statement:
--   The Pts construction uses the coeff subst Mv two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L263-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L263-L270

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Pts
open IntegralMvPolynomialLemmas
variable {K : Type} [Field K] {σ : Type} {R : Subring K} {l linv : PowerSeries K}

theorem Formalism.L2.Th1.C.Pts.coeff_substMv_two {τ : Type} (F : MvPowerSeries (Fin 2) K) {a : Fin 2 → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.subst a F) =
      finsum fun d : Fin 2 →₀ ℕ =>
        MvPowerSeries.coeff d F * MvPowerSeries.coeff e (a 0 ^ d 0 * a 1 ^ d 1) := by sorry
