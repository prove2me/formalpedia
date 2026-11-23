-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_AdaptiveSubstitution_pre_eq
-- name    : Formalism.CyclotomicNorms.AdaptiveSubstitution.pre_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:48:48.324691+00:00
-- url     : https://prove2.me/theorems/c72dc805-2e7d-4868-94ee-130c2e525594
-- title:
--   Adaptive Substitution: pre eq
-- statement:
--   The Adaptive Substitution construction uses the pre eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/AdaptiveSubstitutionBound.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/AdaptiveSubstitutionBound.lean#L19-L27

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_AdaptiveSubstitutionBound
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
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.AdaptiveSubstitution

theorem Formalism.CyclotomicNorms.AdaptiveSubstitution.pre_eq (ℓ A : ℕ) (B : List ℕ → ℕ) (n : ℕ) :
    pre ℓ A B n = List.ofFn (fun i : Fin n => step ℓ A B (pre ℓ A B i)) := by sorry
