-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Det_det_three_points_eq_expansion
-- name    : Formalism.L2.Th1.B.Det.det_three_points_eq_expansion
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:00:31.504801+00:00
-- url     : https://prove2.me/theorems/91d4976b-cac5-4e7c-9589-da0db77279ef
-- title:
--   Det: det three points eq expansion
-- statement:
--   The Det construction uses the det three points eq expansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L136-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L136-L144

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Det
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]
local notation "A3" => MvPowerSeries (Fin 3) K

theorem Formalism.L2.Th1.B.Det.det_three_points_eq_expansion (P : PowerSeries K) :
    det3 P = MvPowerSeries.X 0 ^ 3 * (MvPowerSeries.X 1 * Xt P 1 * Yt P 2 -
        Yt P 1 * (MvPowerSeries.X 2 * Xt P 2)) -
      MvPowerSeries.X 0 * Xt P 0 * (MvPowerSeries.X 1 ^ 3 * Yt P 2 -
        Yt P 1 * MvPowerSeries.X 2 ^ 3) +
      Yt P 0 * (MvPowerSeries.X 1 ^ 3 * (MvPowerSeries.X 2 * Xt P 2) -
        MvPowerSeries.X 1 * Xt P 1 * MvPowerSeries.X 2 ^ 3) := by sorry
