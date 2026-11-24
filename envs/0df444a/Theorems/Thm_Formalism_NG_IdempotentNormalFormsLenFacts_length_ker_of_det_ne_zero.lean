-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_length_ker_of_det_ne_zero
-- name    : Formalism.NG.IdempotentNormalFormsLenFacts.length_ker_of_det_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:13:27.50529+00:00
-- url     : https://prove2.me/theorems/1d5e18ca-6d32-40c5-9a41-202bdad986d2
-- title:
--   Idempotent Normal Forms Len Facts: length ker of det ne zero
-- statement:
--   The Idempotent Normal Forms Len Facts construction uses the length ker of det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L123-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L123-L136

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Formalism.NG.IdempotentNormalFormsLenFacts.length_ker_of_det_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι O)
    (hd : A.det ≠ 0) :
    Module.length O (LinearMap.ker (matQ O A)) = addVal O A.det := by sorry
