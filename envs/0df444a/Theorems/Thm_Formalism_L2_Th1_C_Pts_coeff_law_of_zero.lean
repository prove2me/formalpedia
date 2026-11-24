-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Pts_coeff_law_of_zero
-- name    : Formalism.L2.Th1.C.Pts.coeff_law_of_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:44.388469+00:00
-- url     : https://prove2.me/theorems/14a603ed-517b-43d1-8011-482f5dce177b
-- title:
--   Pts: coeff law of zero
-- statement:
--   The Pts construction uses the coeff law of zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L272-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L272-L328

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

theorem Formalism.L2.Th1.C.Pts.coeff_law_of_zero (h : IsLogPair l linv) (d : Fin 2 →₀ ℕ) (hd : d 0 = 0) :
    MvPowerSeries.coeff d
        (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) =
      MvPowerSeries.coeff d (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) := by sorry
