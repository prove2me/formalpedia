-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Det_pderiv_two_det_three_points
-- name    : Formalism.L2.Th1.B.Det.pderiv_two_det_three_points
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:00:36.792053+00:00
-- url     : https://prove2.me/theorems/5a17b7ac-8c4d-4c22-9c8b-0546dd8d1c9e
-- title:
--   Det: pderiv two det three points
-- statement:
--   The Det construction uses the pderiv two det three points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L204-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L204-L218

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

theorem Formalism.L2.Th1.B.Det.pderiv_two_det_three_points (P : PowerSeries K) :
    pd 2 (det3 P) = MvPowerSeries.X 0 ^ 3 * (MvPowerSeries.X 1 * Xt P 1 * dYt P 2 -
        Yt P 1 * (Xt P 2 + MvPowerSeries.X 2 * dXt P 2)) -
      MvPowerSeries.X 0 * Xt P 0 * (MvPowerSeries.X 1 ^ 3 * dYt P 2 -
        Yt P 1 * (3 * MvPowerSeries.X 2 ^ 2)) +
      Yt P 0 * (MvPowerSeries.X 1 ^ 3 * (Xt P 2 + MvPowerSeries.X 2 * dXt P 2) -
        MvPowerSeries.X 1 * Xt P 1 * (3 * MvPowerSeries.X 2 ^ 2)) := by sorry
