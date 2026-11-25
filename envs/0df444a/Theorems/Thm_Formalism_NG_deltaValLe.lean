-- Prove2me | Theorems.Thm_Formalism_NG_deltaValLe
-- name    : Formalism.NG.deltaValLe
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:51:45.105173+00:00
-- url     : https://prove2.me/theorems/538d8f8a-47ac-491d-9f28-73273ce6f5c8
-- title:
--   NG: delta Val Le
-- statement:
--   The NG construction uses the delta Val Le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ProdEraseZero.lean#L104-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ProdEraseZero.lean#L104-L108

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ProdEraseZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.NG

theorem Formalism.NG.deltaValLe : StatDeltaValLe := by sorry
