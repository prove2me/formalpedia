-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_relaxMap_apply
-- name    : Formalism.NG.IdempotentNormalFormsRhoFacts.relaxMap_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:13:50.55249+00:00
-- url     : https://prove2.me/theorems/c7f6e4fc-bb6f-4668-9272-2752c6140680
-- title:
--   Idempotent Normal Forms Rho Facts: relax Map apply
-- statement:
--   The Idempotent Normal Forms Rho Facts construction uses the relax Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthEqKerAddRange.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthEqKerAddRange.lean#L88-L91

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

theorem Formalism.NG.IdempotentNormalFormsRhoFacts.relaxMap_apply (x : ↥(Q ⊓ ⨅ w ∈ what₂, (F' w).comap (res w))) (w : what₂) :
    relaxMap what₂ res F F' Q x w =
      Submodule.Quotient.mk ⟨res w.1 x.1, ((mem_sel what₂ res F' Q x.1).mp x.2).2 w.1 w.2⟩ := by sorry
