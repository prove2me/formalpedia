-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Wr_eq_zero_of_wronsk
-- name    : Formalism.L2.Th1.B.Wr.eq_zero_of_wronsk
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:01:16.37193+00:00
-- url     : https://prove2.me/theorems/b24f939c-e719-40eb-a1c3-ab1867eb64cd
-- title:
--   Wr: eq zero of wronsk
-- statement:
--   The Wr construction uses the eq zero of wronsk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/XTwoDvdOfRestrictThirdZero.lean#L83-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/XTwoDvdOfRestrictThirdZero.lean#L83-L129

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_XTwoDvdOfRestrictThirdZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Wr
open MvPowerSeries
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.B.Wr.eq_zero_of_wronsk {Q B : MvPowerSeries (Fin 3) K} (hw : Q * pd 2 B = B * pd 2 Q)
    (hQ : ev3 Q = 0) (hB : ev3 B ≠ 0) : Q = 0 := by sorry
