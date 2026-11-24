-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_det_three_points
-- name    : Formalism.L2.Th1.B.Fs.eval_last_zero_det_three_points
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:59:39.724467+00:00
-- url     : https://prove2.me/theorems/1dbe5685-31d5-4897-8130-5687d2e1a9f1
-- title:
--   Fs: eval last zero det three points
-- statement:
--   The Fs construction uses the eval last zero det three points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L178-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RealAdelicInertTransportTypeFormsEqAlt.lean#L178-L183

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Fs
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]
local notation "A3" => MvPowerSeries (Fin 3) K

theorem Formalism.L2.Th1.B.Fs.eval_last_zero_det_three_points (P : PowerSeries K) :
    ev3H (det3 P) = -2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1) * wp3 P 0 1 := by sorry
