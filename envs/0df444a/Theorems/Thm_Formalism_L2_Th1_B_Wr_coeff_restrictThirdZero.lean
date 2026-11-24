-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Wr_coeff_restrictThirdZero
-- name    : Formalism.L2.Th1.B.Wr.coeff_restrictThirdZero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:01:16.043738+00:00
-- url     : https://prove2.me/theorems/6afa2a4d-6029-46b6-b936-d4606de5b0d9
-- title:
--   Wr: coeff restrict Third Zero
-- statement:
--   The Wr construction uses the coeff restrict Third Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/XTwoDvdOfRestrictThirdZero.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/XTwoDvdOfRestrictThirdZero.lean#L27-L31

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

theorem Formalism.L2.Th1.B.Wr.coeff_restrictThirdZero (h : MvPowerSeries (Fin 3) K) (n : Fin 3 →₀ ℕ) (hn : n 2 = 0) :
    coeff n (ev3 h) = coeff n h := by sorry
