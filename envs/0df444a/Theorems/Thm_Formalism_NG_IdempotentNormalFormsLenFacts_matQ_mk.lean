-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_matQ_mk
-- name    : Formalism.NG.IdempotentNormalFormsLenFacts.matQ_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:03.813408+00:00
-- url     : https://prove2.me/theorems/5c14147a-2426-4b02-a849-e1cbcc114e2d
-- title:
--   Idempotent Normal Forms Len Facts: mat Q mk
-- statement:
--   The Idempotent Normal Forms Len Facts construction uses the mat Q mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L33-L42

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

theorem Formalism.NG.IdempotentNormalFormsLenFacts.matQ_mk {ι : Type*} [Fintype ι] (A : Matrix ι ι O) (y : ι → FractionRing O) :
    matQ O A (fun i => (Submodule.Quotient.mk (y i) : KO O)) =
      fun i => (Submodule.Quotient.mk ((A.map (algebraMap O (FractionRing O)) *ᵥ y) i) : KO O) := by sorry
