-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_ker_phi
-- name    : Formalism.NG.IdempotentNormalFormsLenFacts.ker_phi
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:13:21.877247+00:00
-- url     : https://prove2.me/theorems/ce7414d8-8ea4-4e66-a45f-76a020e96efa
-- title:
--   Idempotent Normal Forms Len Facts: ker phi
-- statement:
--   The Idempotent Normal Forms Len Facts construction uses the ker phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L101-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L101-L121

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

theorem Formalism.NG.IdempotentNormalFormsLenFacts.ker_phi (A : Matrix ι ι O) (hd : A.det ≠ 0) :
    LinearMap.ker (phi A) = LinearMap.range (Matrix.mulVecLin A) := by sorry
