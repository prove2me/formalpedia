-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_length_ker_of_det_eq_zero
-- name    : Formalism.NG.IdempotentNormalFormsLenFacts.length_ker_of_det_eq_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:13:23.866858+00:00
-- url     : https://prove2.me/theorems/a541d9e3-174a-470c-a0c9-eb1f73b7fc8f
-- title:
--   Idempotent Normal Forms Len Facts: length ker of det eq zero
-- statement:
--   The Idempotent Normal Forms Len Facts construction uses the length ker of det eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L138-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L138-L208

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

theorem Formalism.NG.IdempotentNormalFormsLenFacts.length_ker_of_det_eq_zero (A : Matrix ι ι O) (hd : A.det = 0) :
    Module.length O (LinearMap.ker (matQ O A)) = ⊤ := by sorry
