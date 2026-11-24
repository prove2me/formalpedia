-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_length_pi_rows
-- name    : Formalism.NG.IdempotentNormalFormsRhoFacts.length_pi_rows
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:13:42.108894+00:00
-- url     : https://prove2.me/theorems/50d5e6bc-1b06-4317-a3e4-de712c8b1f93
-- title:
--   Idempotent Normal Forms Rho Facts: length pi rows
-- statement:
--   The Idempotent Normal Forms Rho Facts construction uses the length pi rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthEqKerAddRange.lean#L109-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthEqKerAddRange.lean#L109-L114

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

theorem Formalism.NG.IdempotentNormalFormsRhoFacts.length_pi_rows :
    Module.length O ((w : what₂) → (F' w.1 ⧸ (F w.1).comap (F' w.1).subtype)) =
      ∑ w ∈ what₂, Module.length O (F' w ⧸ (F w).comap (F' w).subtype) := by sorry
