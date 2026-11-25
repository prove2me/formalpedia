-- Prove2me | Theorems.Thm_Formalism_NG_idempotentNormalForms_fact
-- name    : Formalism.NG.idempotentNormalForms_fact
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:51:24.64546+00:00
-- url     : https://prove2.me/theorems/e36db829-207d-5704-b03d-5f096194b171
-- title:
--   NG: idempotent Normal Forms fact
-- statement:
--   The NG construction uses the idempotent Normal Forms fact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/CharacterColumnKernelLengthBound.lean#L77-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/CharacterColumnKernelLengthBound.lean#L77-L117

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelLengthBound
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ProdEraseZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CharacterColumnKernelLengthBound
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

theorem Formalism.NG.idempotentNormalForms_fact : characterColumnKernelBlockBound := by sorry
