-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_addVal_prod
-- name    : Formalism.NG.IdempotentNormalFormsLenFacts.addVal_prod
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:23.784512+00:00
-- url     : https://prove2.me/theorems/6125a2a7-3709-58ea-8a54-5d9f39d90dc4
-- title:
--   Idempotent Normal Forms Len Facts: add Val prod
-- statement:
--   The Idempotent Normal Forms Len Facts construction uses the add Val prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L19-L21

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Lemmata_SecondBlockLemmaA_Imports
import Definitions.Def_Lemmata_AddValuationProducts_AddValProd
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Matrix
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdempotentNormalFormsLenFacts
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem Formalism.NG.IdempotentNormalFormsLenFacts.addVal_prod {ι : Type*} (s : Finset ι) (a : ι → O) :
    addVal O (∏ i ∈ s, a i) = ∑ i ∈ s, addVal O (a i) := by sorry
