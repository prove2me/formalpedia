-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_AdaptiveSubstitution_mem_pre
-- name    : Formalism.CyclotomicNorms.AdaptiveSubstitution.mem_pre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:44.821381+00:00
-- url     : https://prove2.me/theorems/6a874dcb-8f61-4a81-b5e9-7314a6595cb0
-- title:
--   Adaptive Substitution: mem pre
-- statement:
--   The Adaptive Substitution construction uses the mem pre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/AdaptiveSubstitutionBound.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/AdaptiveSubstitutionBound.lean#L29-L32

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

theorem Formalism.CyclotomicNorms.AdaptiveSubstitution.mem_pre (ℓ A : ℕ) (B : List ℕ → ℕ) {i n : ℕ} (h : i < n) :
    step ℓ A B (pre ℓ A B i) ∈ pre ℓ A B n := by sorry
