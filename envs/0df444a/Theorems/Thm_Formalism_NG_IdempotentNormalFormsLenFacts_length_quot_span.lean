-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_length_quot_span
-- name    : Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:33:37.785071+00:00
-- url     : https://prove2.me/theorems/8c458a78-3d85-4c45-80a7-9df9bf16a28c
-- title:
--   Idempotent Normal Forms Len Facts: length quot span
-- statement:
--   The Idempotent Normal Forms Len Facts construction uses the length quot span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L15-L17

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

theorem Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span (a : O) :
    Module.length O (O ⧸ Ideal.span ({a} : Set O)) = addVal O a := by sorry
