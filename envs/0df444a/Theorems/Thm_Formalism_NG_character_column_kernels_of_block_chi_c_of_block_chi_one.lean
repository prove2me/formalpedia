-- Prove2me | Theorems.Thm_Formalism_NG_character_column_kernels_of_block_chi_c_of_block_chi_one
-- name    : Formalism.NG.character_column_kernels_of_block_chi_c_of_block_chi_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:16:55.764993+00:00
-- url     : https://prove2.me/theorems/6a673284-5c13-49d2-9376-095ed3ddf7f3
-- title:
--   NG: character column kernels of block chi c of block chi one
-- statement:
--   The NG construction uses the character column kernels of block chi c of block chi one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/CharacterColumnKernelsOfBlockChiCOfBlockChiOne.lean#L239-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/CharacterColumnKernelsOfBlockChiCOfBlockChiOne.lean#L239-L282

import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalColumn
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockRhoFull
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneFullOf
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CharacterColumnKernelsOfBlockChiCOfBlockChiOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.NG

theorem Formalism.NG.character_column_kernels_of_block_chi_c_of_block_chi_one (hC : StatBlockChiCFull.{0, 0, 0, 0, 0, 0})
    (hOne : StatBlockChiOneFull.{0, 0, 0, 0, 0, 0}) : characterColumnKernelEqualityForm := by sorry
