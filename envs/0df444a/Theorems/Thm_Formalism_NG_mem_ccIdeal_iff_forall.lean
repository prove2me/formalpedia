-- Prove2me | Theorems.Thm_Formalism_NG_mem_ccIdeal_iff_forall
-- name    : Formalism.NG.mem_ccIdeal_iff_forall
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:05.228035+00:00
-- url     : https://prove2.me/theorems/d72e98b7-e1c1-4668-b52d-9f004e5a32e9
-- title:
--   NG: mem cc Ideal iff forall
-- statement:
--   The NG construction uses the mem cc Ideal iff forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/MemCcIdealIffForall.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/MemCcIdealIffForall.lean#L9-L19

import Definitions.Def_Formalism_CharacterColumnKernels_StatementBC
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_MemCcIdealIffForall
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

theorem Formalism.NG.mem_ccIdeal_iff_forall {O : Type*} [CommRing O] {X : Type*} (T : Subalgebra O (X → O))
    (Z : Set X) (c : T) : c ∈ ccIdeal T Z ↔ ∀ x ∉ Z, (c : X → O) x = 0 := by sorry
