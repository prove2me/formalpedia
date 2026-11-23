-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_length_quot_eq_addVal_det
-- name    : Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_eq_addVal_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:14.688104+00:00
-- url     : https://prove2.me/theorems/83c30c24-7dec-4169-9c03-f3ff30cf05b5
-- title:
--   Idempotent Normal Forms Len Facts: length quot eq add Val det
-- statement:
--   The Idempotent Normal Forms Len Facts construction uses the length quot eq add Val det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L23-L27

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

theorem Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_eq_addVal_det {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : Submodule O (ι → O)) (e : (ι → O) ≃ₗ[O] N) :
    Module.length O ((ι → O) ⧸ N) =
      addVal O (LinearMap.det (N.subtype ∘ₗ (e : (ι → O) →ₗ[O] N))) := by sorry
