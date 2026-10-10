-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicBellmanValue_policy_attains
-- name    : ActuarialValuation.finiteEntropicBellmanValue_policy_attains
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:53:10.071079+00:00
-- url     : https://prove2.me/theorems/37b6b511-52ba-43f2-8829-4d10222e6f1b
-- title:
--   An optimal deterministic nonstationary Markov policy exists for the horizon
-- statement:
--   Because the action menu is finite and nonempty, at each backward-induction layer every state admits a least-risk-cost action. Choosing one for each state and remaining horizon yields a deterministic nonstationary Markov control whose recursively valued policy cost equals the Bellman value in all starting states simultaneously.
--
--   **Mathematical statement**
--
--   $$
--   \exists\pi^*,\ \forall s,\ J^{\pi^*}_n(s)=V_n(s)
--   $$
-- source:
--   Bäuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), Definition 4.6, Theorem 4.7, equation (4.2), DOI https://doi.org/10.1016/j.ejor.2021.04.030; Bäuerle and Jaśkiewicz (2024), entropic certainty equivalent, Example 1(a), equation (2), DOI https://doi.org/10.1007/s00186-024-00857-0; derived finite-state discrete-time insurer cost specialisation

import Mathlib
import Definitions.Def_actuarial_finiteEntropicBellmanValue
import Definitions.Def_actuarial_finiteEntropicPolicyValue

namespace ActuarialValuation

theorem finiteEntropicBellmanValue_policy_attains {S A : Type*}
  [Fintype S] [Fintype A] [Nonempty A]
  (P : S → A → S → ℝ)
  (cost : S → A → S → ℝ) (beta gamma : ℝ)
  (terminal : S → ℝ) (n : ℕ)
  (hP : ∀ s a t, 0 ≤ P s a t)
  (hsum : ∀ s a, (∑ t : S, P s a t) = 1)
  (hbeta : 0 ≤ beta) (hgamma : 0 < gamma) :
  ∃ policy : ℕ → S → A, ∀ s : S,
    finiteEntropicPolicyValue P cost beta gamma terminal policy n s =
      finiteEntropicBellmanValue P cost beta gamma terminal n s := by sorry

end ActuarialValuation
