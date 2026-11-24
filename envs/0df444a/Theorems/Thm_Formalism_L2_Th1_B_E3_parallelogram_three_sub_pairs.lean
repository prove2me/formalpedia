-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_E3_parallelogram_three_sub_pairs
-- name    : Formalism.L2.Th1.B.E3.parallelogram_three_sub_pairs
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:01:50.858798+00:00
-- url     : https://prove2.me/theorems/e4319850-18ca-4957-a72b-66ff492cadef
-- title:
--   E3: parallelogram three sub pairs
-- statement:
--   The E3 construction uses the parallelogram three sub pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/FirstLevelOfThreeVarParallelogram.lean#L11-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/FirstLevelOfThreeVarParallelogram.lean#L11-L27

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_FirstLevelOfThreeVarParallelogram
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.E3
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)

theorem Formalism.L2.Th1.B.E3.parallelogram_three_sub_pairs {K : Type} [NormedField K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (hF : MvPowerSeries.constantCoeff F = 0) (i f : PowerSeries K)
    (hi : PowerSeries.constantCoeff i = 0) :
    par3 F i f -
        MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1]
          (par F i f) -
        MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2]
          (par F i f) -
        MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2]
          (par F i f) =
      d1 F (cob F f) := by sorry
