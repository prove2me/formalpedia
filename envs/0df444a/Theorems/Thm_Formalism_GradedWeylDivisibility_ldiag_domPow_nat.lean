-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_domPow_nat
-- name    : Formalism.GradedWeylDivisibility.ldiag_domPow_nat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:52.353803+00:00
-- url     : https://prove2.me/theorems/25f6971b-3f71-41b0-82e2-26ced2db6c64
-- title:
--   Graded Weyl Divisibility: ldiag dom Pow nat
-- statement:
--   The Graded Weyl Divisibility construction uses the ldiag dom Pow nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DomPow.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DomPow.lean#L53-L58

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

theorem Formalism.GradedWeylDivisibility.ldiag_domPow_nat (t : ℕ → ℝ) (ht0 : ∀ a, 0 ≤ t a) (ht : Antitone t) (μ lam : ℕ → ℕ) (N : ℕ)
    (hS : ∀ k ≤ N, ∑ a ∈ range k, μ a ≤ ∑ a ∈ range k, lam a)
    (hT : ∑ a ∈ range N, μ a = ∑ a ∈ range N, lam a) :
    ∏ a ∈ range N, t a ^ μ a ≤ ∏ a ∈ range N, t a ^ lam a := by sorry
