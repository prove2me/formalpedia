-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Wr_sh_sub
-- name    : Formalism.L2.Th1.B.Wr.sh_sub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:01:22.753556+00:00
-- url     : https://prove2.me/theorems/36a52b10-9a00-4b37-962b-5ab67a3db75e
-- title:
--   Wr: sh sub
-- statement:
--   The Wr construction uses the sh sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/XTwoDvdOfRestrictThirdZero.lean#L173-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/XTwoDvdOfRestrictThirdZero.lean#L173-L175

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

theorem Formalism.L2.Th1.B.Wr.sh_sub (f g : MvPowerSeries (Fin 3) K) : sh (f - g) = sh f - sh g := by sorry
