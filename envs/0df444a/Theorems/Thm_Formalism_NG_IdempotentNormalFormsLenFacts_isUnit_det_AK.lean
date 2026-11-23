-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_isUnit_det_AK
-- name    : Formalism.NG.IdempotentNormalFormsLenFacts.isUnit_det_AK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:05.960753+00:00
-- url     : https://prove2.me/theorems/4efcf2ef-17b8-471b-81a1-b12dbc2ead0d
-- title:
--   Idempotent Normal Forms Len Facts: is Unit det AK
-- statement:
--   The Idempotent Normal Forms Len Facts construction uses the is Unit det AK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L48-L50

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

theorem Formalism.NG.IdempotentNormalFormsLenFacts.isUnit_det_AK (A : Matrix ι ι O) (hd : A.det ≠ 0) : IsUnit (AK A).det := by sorry
