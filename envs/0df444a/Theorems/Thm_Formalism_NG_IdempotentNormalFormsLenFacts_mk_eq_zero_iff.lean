-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_mk_eq_zero_iff
-- name    : Formalism.NG.IdempotentNormalFormsLenFacts.mk_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:20.864187+00:00
-- url     : https://prove2.me/theorems/61bf1da1-377b-4e01-9e07-88a87757102c
-- title:
--   Idempotent Normal Forms Len Facts: mk eq zero iff
-- statement:
--   The Idempotent Normal Forms Len Facts construction uses the mk eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean#L29-L31

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

theorem Formalism.NG.IdempotentNormalFormsLenFacts.mk_eq_zero_iff (y : FractionRing O) :
    (Submodule.Quotient.mk y : KO O) = 0 ↔ ∃ x : O, algebraMap O (FractionRing O) x = y := by sorry
