-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_AdaptiveSubstitution_exists_exps_adaptive
-- name    : Formalism.CyclotomicNorms.AdaptiveSubstitution.exists_exps_adaptive
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:39.482837+00:00
-- url     : https://prove2.me/theorems/6b845d95-5dfb-4483-a1d6-f86de2c53bc1
-- title:
--   Adaptive Substitution: exists exps adaptive
-- statement:
--   The Adaptive Substitution construction uses the exists exps adaptive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/AdaptiveSubstitutionBound.lean#L34-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/AdaptiveSubstitutionBound.lean#L34-L81

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

theorem Formalism.CyclotomicNorms.AdaptiveSubstitution.exists_exps_adaptive (ℓ : ℕ) {r s : ℕ} (hℓ : 2 ≤ ℓ) (α : Fin s → Fin r →₀ ℕ)
    (B : List ℕ → ℕ) :
    ∃ e : Fin r → ℕ, StrictMono e ∧
      (∀ j : Fin r, B (List.ofFn fun i : Fin (j : ℕ) => e (Fin.castLE (Nat.le_of_lt j.isLt) i)) ≤ e j) ∧
      ∀ t j, ∑ i ∈ univ.filter (· < j), α t i * ℓ ^ e i < ℓ ^ e j := by sorry
