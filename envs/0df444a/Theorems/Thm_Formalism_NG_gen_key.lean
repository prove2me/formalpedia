-- Prove2me | Theorems.Thm_Formalism_NG_gen_key
-- name    : Formalism.NG.gen_key
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:36.650876+00:00
-- url     : https://prove2.me/theorems/1a824f80-5b65-40a2-8127-1ea1cecec2bc
-- title:
--   NG: gen key
-- statement:
--   The NG construction uses the gen key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GenRelMapApply.lean#L29-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GenRelMapApply.lean#L29-L99

import Definitions.Def_Formalism_CharacterColumnKernels_StatementG
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenRelMapApply
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
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem Formalism.NG.gen_key {M G : Type} [Fintype M] [DecidableEq M] [Fintype G] [DecidableEq G]
    (A : Matrix M G O) : ∃ (n : ℕ) (U : Matrix M M O) (f : Fin n ↪ M) (e : Fin n ↪ G),
      (∃ C0 : Matrix G M O, IsUnit (Matrix.of fun p q => (C0 * U) (e p) (f q)).det) ∧
      ∀ C' : Matrix G M O, IsUnit (Matrix.of fun p q => (C' * U) (e p) (f q)).det →
        LinearMap.ker (relMap O (KO O) (C' * A)) = LinearMap.ker (relMap O (KO O) A) := by sorry
