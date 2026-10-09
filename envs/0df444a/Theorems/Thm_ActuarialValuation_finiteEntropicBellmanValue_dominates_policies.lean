-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicBellmanValue_dominates_policies
-- name    : ActuarialValuation.finiteEntropicBellmanValue_dominates_policies
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:49:29.106591+00:00
-- url     : https://prove2.me/theorems/9f60c1db-03a1-4d42-bb42-6a0b40192c5a
-- title:
--   Risk-sensitive Bellman value dominates every fixed Markov policy in cost minimisation
-- statement:
--   With nonnegative normalised transition rows, positive entropic risk aversion and nonnegative continuation discount, backward induction and monotonicity show that optimal finite-horizon cost at each state cannot exceed the value of any deterministic remaining-horizon Markov policy. This does not compare to arbitrary history-dependent or randomised policies.
--
--   **Mathematical statement**
--
--   $$
--   V_n(s)\le J^\pi_n(s)
--   $$
-- source:
--   Bäuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), Definition 4.6, Theorem 4.7, equation (4.2), DOI https://doi.org/10.1016/j.ejor.2021.04.030; Bäuerle and Jaśkiewicz (2024), entropic certainty equivalent, Example 1(a), equation (2), DOI https://doi.org/10.1007/s00186-024-00857-0; derived finite-state discrete-time insurer cost specialisation

import Mathlib
import Definitions.Def_actuarial_finiteEntropicBellmanValue
import Definitions.Def_actuarial_finiteEntropicPolicyValue

namespace ActuarialValuation

theorem finiteEntropicBellmanValue_dominates_policies {S A : Type*}
  [Fintype S] [Fintype A] [Nonempty A]
  (P : S → A → S → ℝ)
  (cost : S → A → S → ℝ) (beta gamma : ℝ)
  (terminal : S → ℝ) (n : ℕ)
  (hP : ∀ s a t, 0 ≤ P s a t)
  (hsum : ∀ s a, (∑ t : S, P s a t) = 1)
  (hbeta : 0 ≤ beta) (hgamma : 0 < gamma)
  (policy : ℕ → S → A) (s : S) :
  finiteEntropicBellmanValue P cost beta gamma terminal n s ≤
    finiteEntropicPolicyValue P cost beta gamma terminal policy n s := by sorry

end ActuarialValuation
