-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Det_triple_lintegral_eq
-- name    : Formalism.L2.Th1.B.Det.triple_lintegral_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:47:50.269538+00:00
-- url     : https://prove2.me/theorems/56159889-815d-53bf-883a-20f04941e48a
-- title:
--   Det: triple lintegral eq
-- statement:
--   The Det construction uses the triple lintegral eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L66-L68

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
import Theorems.Thm_Formalism_L2_Th1_B_Add0_triple_lintegral_eq
import Theorems.Thm_Formalism_L2_Th1_B_Add1_triple_lintegral_eq

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

theorem Formalism.L2.Th1.B.Det.triple_lintegral_eq (x : Fin 3) (f : PowerSeries K) :
    (at1 x f : A3) = PowerSeries.substAlgHom (PowerSeries.HasSubst.X x) f := by sorry
