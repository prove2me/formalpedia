-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Add1_restrictSecondZero_inVar_one
-- name    : Formalism.L2.Th1.B.Add1.restrictSecondZero_inVar_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:50.560751+00:00
-- url     : https://prove2.me/theorems/af2971ed-d26a-48b0-9462-b0aaf9933c85
-- title:
--   Add1: restrict Second Zero in Var one
-- statement:
--   The Add1 construction uses the restrict Second Zero in Var one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RestrictSecondZeroInVarOne.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RestrictSecondZeroInVarOne.lean#L61-L64

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RestrictSecondZeroInVarOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Add1
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.B.Add1.restrictSecondZero_inVar_one {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    ev0 (at1 1 f) = 0 := by sorry
