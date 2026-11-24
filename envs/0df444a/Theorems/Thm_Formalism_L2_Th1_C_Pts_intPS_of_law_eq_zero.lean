-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Pts_intPS_of_law_eq_zero
-- name    : Formalism.L2.Th1.C.Pts.intPS_of_law_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:05.732606+00:00
-- url     : https://prove2.me/theorems/fa4b7fb3-8167-4d2c-8a09-2d9baf8c9bff
-- title:
--   Pts: int PS of law eq zero
-- statement:
--   The Pts construction uses the int PS of law eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L346-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L346-L387

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

theorem Formalism.L2.Th1.C.Pts.intPS_of_law_eq_zero {F : MvPowerSeries (Fin 2) K} (hF : IntMv R F)
    (hF0 : ∀ d : Fin 2 →₀ ℕ, d 0 = 0 → MvPowerSeries.coeff d F =
      MvPowerSeries.coeff d (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K))
    {i : PowerSeries K} (hi : PowerSeries.constantCoeff i = 0)
    (hz : MvPowerSeries.subst (![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K) F = 0) :
    IntPS R i := by sorry
