-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_map_mulVec_fun
-- name    : Formalism.NG.IdempotentNormalFormsLenFacts.map_mulVec_fun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:21.189709+00:00
-- url     : https://prove2.me/theorems/909b73a1-7de2-41dd-8d85-e47c91e81a2f
-- title:
--   Idempotent Normal Forms Len Facts: map mul Vec fun
-- statement:
--   The Idempotent Normal Forms Len Facts construction uses the map mul Vec fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L76-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L76-L80

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

theorem Formalism.NG.IdempotentNormalFormsLenFacts.map_mulVec_fun (A : Matrix ι ι O) (z : ι → O) :
    (fun i => algebraMap O (FractionRing O) ((A *ᵥ z) i)) =
      AK A *ᵥ (fun j => algebraMap O (FractionRing O) (z j)) := by sorry
