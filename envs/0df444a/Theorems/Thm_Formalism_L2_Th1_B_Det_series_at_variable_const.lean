-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Det_series_at_variable_const
-- name    : Formalism.L2.Th1.B.Det.series_at_variable_const
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:48:13.083465+00:00
-- url     : https://prove2.me/theorems/0af9c772-10da-4a7a-adf0-c88defef20bf
-- title:
--   Det: series at variable const
-- statement:
--   The Det construction uses the series at variable const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L70-L72

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
import Theorems.Thm_Formalism_L2_Th1_B_Add0_series_at_variable_const

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

theorem Formalism.L2.Th1.B.Det.series_at_variable_const (x : Fin 3) (c : K) : (at1 x (PowerSeries.C c) : A3) = MvPowerSeries.C c := by sorry
