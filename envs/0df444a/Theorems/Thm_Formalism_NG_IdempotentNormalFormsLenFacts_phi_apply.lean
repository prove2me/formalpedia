-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_phi_apply
-- name    : Formalism.NG.IdempotentNormalFormsLenFacts.phi_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:15.098639+00:00
-- url     : https://prove2.me/theorems/765876bd-ae96-48dd-ba6d-10cf697400cc
-- title:
--   Idempotent Normal Forms Len Facts: phi apply
-- statement:
--   The Idempotent Normal Forms Len Facts construction uses the phi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L72-L74

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

theorem Formalism.NG.IdempotentNormalFormsLenFacts.phi_apply (A : Matrix ι ι O) (x : ι → O) :
    phi A x = fun i => (Submodule.Quotient.mk
      (((AK A)⁻¹ *ᵥ (fun j => algebraMap O (FractionRing O) (x j))) i) : KO O) := by sorry
