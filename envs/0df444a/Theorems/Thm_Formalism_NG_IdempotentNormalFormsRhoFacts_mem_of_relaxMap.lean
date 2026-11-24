-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_mem_of_relaxMap
-- name    : Formalism.NG.IdempotentNormalFormsRhoFacts.mem_of_relaxMap
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:14:07.738647+00:00
-- url     : https://prove2.me/theorems/d5fc2acd-d32b-4af8-a58a-f9ba2557f0f8
-- title:
--   Idempotent Normal Forms Rho Facts: mem of relax Map
-- statement:
--   The Idempotent Normal Forms Rho Facts construction uses the mem of relax Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthEqKerAddRange.lean#L93-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthEqKerAddRange.lean#L93-L98

import Definitions.Def_Formalism_CharacterColumnKernels_StatementRho
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdempotentNormalFormsRhoFacts
variable {O C ι : Type*} [CommRing O] [AddCommGroup C] [Module O C]
  {Cw : ι → Type*} [∀ w, AddCommGroup (Cw w)] [∀ w, Module O (Cw w)]
  (what₂ : Finset ι) (res : ∀ w, C →ₗ[O] Cw w) (F F' : ∀ w, Submodule O (Cw w)) (Q : Submodule O C)

theorem Formalism.NG.IdempotentNormalFormsRhoFacts.mem_of_relaxMap (x : ↥(Q ⊓ ⨅ w ∈ what₂, (F' w).comap (res w)))
    (hx : relaxMap what₂ res F F' Q x = 0) : x.1 ∈ Q ⊓ ⨅ w ∈ what₂, (F w).comap (res w) := by sorry
