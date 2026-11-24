-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Det_partialDeriv_inVar_of_ne
-- name    : Formalism.L2.Th1.B.Det.partialDeriv_inVar_of_ne
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:00:28.959033+00:00
-- url     : https://prove2.me/theorems/04686468-1dc7-41f5-9862-00608e156a59
-- title:
--   Det: partial Deriv in Var of ne
-- statement:
--   The Det construction uses the partial Deriv in Var of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L83-L85

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
import Theorems.Thm_Formalism_L2_Th1_B_Add0_partialDeriv_inVar_of_ne
import Theorems.Thm_Formalism_L2_Th1_B_Add1_partialDeriv_inVar_of_ne

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

theorem Formalism.L2.Th1.B.Det.partialDeriv_inVar_of_ne {i x : Fin 3} (h : x ≠ i) (f : PowerSeries K) : pd i (at1 x f : A3) = 0 := by sorry
