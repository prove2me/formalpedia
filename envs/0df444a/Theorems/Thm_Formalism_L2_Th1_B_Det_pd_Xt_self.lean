-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Det_pd_Xt_self
-- name    : Formalism.L2.Th1.B.Det.pd_Xt_self
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:01:07.665615+00:00
-- url     : https://prove2.me/theorems/c4e8e716-4416-4f9c-979f-bcd79c6578d1
-- title:
--   Det: pd Xt self
-- statement:
--   The Det construction uses the pd Xt self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L102-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/Wp3ApplyEqSqMulSubSqMul.lean#L102-L107

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

theorem Formalism.L2.Th1.B.Det.pd_Xt_self (P : PowerSeries K) (j : Fin 3) :
    MvPowerSeries.pderiv K j (Xt P j) = dXt P j := by sorry
