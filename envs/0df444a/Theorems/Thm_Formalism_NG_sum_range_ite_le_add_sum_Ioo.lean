-- Prove2me | Theorems.Thm_Formalism_NG_sum_range_ite_le_add_sum_Ioo
-- name    : Formalism.NG.sum_range_ite_le_add_sum_Ioo
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:29.966829+00:00
-- url     : https://prove2.me/theorems/711763a1-c896-4fc4-b4d4-dc9e83aaf80b
-- title:
--   NG: sum range ite le add sum Ioo
-- statement:
--   The NG construction uses the sum range ite le add sum Ioo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/CharacterColumnKernelsOfBlockChiCOfBlockChiOne.lean#L12-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/CharacterColumnKernelsOfBlockChiCOfBlockChiOne.lean#L12-L31

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

theorem Formalism.NG.sum_range_ite_le_add_sum_Ioo (t : ℕ) (a : ℕ∞) (Sha : ℕ → ℕ∞) :
    ∑ i ∈ range t, (if i + 1 = 1 then a else Sha (i + 1 - 1)) ≤ a + ∑ e ∈ Ioo 0 t, Sha e := by sorry
