-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_antitone_prod_pow_dominance
-- name    : Formalism.GradedWeylDivisibility.antitone_prod_pow_dominance
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:35.484851+00:00
-- url     : https://prove2.me/theorems/aeff4045-ab86-4275-84ec-7b16a9b51dec
-- title:
--   Graded Weyl Divisibility: antitone prod pow dominance
-- statement:
--   The Graded Weyl Divisibility construction uses the antitone prod pow dominance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DomPow.lean#L9-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DomPow.lean#L9-L51

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow
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
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.antitone_prod_pow_dominance (t : ℕ → ℝ) (ht0 : ∀ a, 0 ≤ t a) (ht : Antitone t) (μ lam : ℕ → ℕ) :
    ∀ N : ℕ, (∀ k ≤ N, ∑ a ∈ range k, μ a ≤ ∑ a ∈ range k, lam a) →
      ∀ c : ℝ, 0 ≤ c → (∀ a < N, c ≤ t a) →
      (∏ a ∈ range N, t a ^ μ a) * c ^ (∑ a ∈ range N, lam a - ∑ a ∈ range N, μ a) ≤
        ∏ a ∈ range N, t a ^ lam a := by sorry
