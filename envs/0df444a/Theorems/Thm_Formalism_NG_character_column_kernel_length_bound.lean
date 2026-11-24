-- Prove2me | Theorems.Thm_Formalism_NG_character_column_kernel_length_bound
-- name    : Formalism.NG.character_column_kernel_length_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:23:30.00383+00:00
-- url     : https://prove2.me/theorems/3428e8fe-f35e-4cc0-9419-3a672711656c
-- title:
--   NG: character column kernel length bound
-- statement:
--   The NG construction uses the character column kernel length bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/CharacterColumnKernelLengthBound.lean#L57-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/CharacterColumnKernelLengthBound.lean#L57-L70

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

theorem Formalism.NG.character_column_kernel_length_bound : characterColumnKernelLengthBound := by sorry
