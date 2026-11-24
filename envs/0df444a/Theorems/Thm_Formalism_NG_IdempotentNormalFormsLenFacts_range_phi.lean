-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_range_phi
-- name    : Formalism.NG.IdempotentNormalFormsLenFacts.range_phi
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:13:38.427896+00:00
-- url     : https://prove2.me/theorems/220aac73-b3eb-4932-b193-3c798c480d80
-- title:
--   Idempotent Normal Forms Len Facts: range phi
-- statement:
--   The Idempotent Normal Forms Len Facts construction uses the range phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L82-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L82-L99

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

theorem Formalism.NG.IdempotentNormalFormsLenFacts.range_phi (A : Matrix ι ι O) (hd : A.det ≠ 0) :
    LinearMap.range (phi A) = LinearMap.ker (matQ O A) := by sorry
