-- Prove2me | Theorems.Thm_Formalism_NG_nGlobal
-- name    : Formalism.NG.nGlobal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:53.838696+00:00
-- url     : https://prove2.me/theorems/1c7f636e-b322-400f-b596-88154f612d44
-- title:
--   NG: n Global
-- statement:
--   The NG construction uses the n Global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SumIteLe.lean#L29-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SumIteLe.lean#L29-L56

import Definitions.Def_Formalism_CharacterColumnKernels_StatementNG
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalConcreteOf
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SumIteLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG

theorem Formalism.NG.nGlobal : StatNGlobal := by sorry
