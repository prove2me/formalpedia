-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Det_wp3_apply_eq_sq_mul_sub_sq_mul
-- name    : Formalism.L2.Th1.B.Det.wp3_apply_eq_sq_mul_sub_sq_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:01:13.127881+00:00
-- url     : https://prove2.me/theorems/a9ab7584-2983-40b3-8c77-66e3eb5dd66e
-- title:
--   Det: wp3 apply eq sq mul sub sq mul
-- statement:
--   The Det construction uses the wp3 apply eq sq mul sub sq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L131-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L131-L134

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

theorem Formalism.L2.Th1.B.Det.wp3_apply_eq_sq_mul_sub_sq_mul (P : PowerSeries K) (j k : Fin 3) :
    wp3 P j k = MvPowerSeries.X j ^ 2 * Xt P k - MvPowerSeries.X k ^ 2 * Xt P j := by sorry
