-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicPolicyValue_succ
-- name    : ActuarialValuation.finiteEntropicPolicyValue_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:46:16.028311+00:00
-- url     : https://prove2.me/theorems/2fc76604-7f91-4cfc-a924-3aab61d46bfa
-- title:
--   One more policy year applies the selected entropic transition cost
-- statement:
--   The policy index n identifies the decision applied when n+1 years remain, with the previous n-year policy valuation as continuation. The stage loss and discounted future policy cost enter jointly inside the exponential. This successor equation is definitionally distinct from the expected-value Bellman recursion in Mission XVII.
--
--   **Mathematical statement**
--
--   $$
--   J^\pi_{n+1}(s)=Q_{\gamma,\beta}(s,\pi(n,s);J^\pi_n)
--   $$
-- source:
--   Bäuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), Definition 4.6, Theorem 4.7, equation (4.2), DOI https://doi.org/10.1016/j.ejor.2021.04.030; Bäuerle and Jaśkiewicz (2024), entropic certainty equivalent, Example 1(a), equation (2), DOI https://doi.org/10.1007/s00186-024-00857-0; derived finite-state discrete-time insurer cost specialisation

import Mathlib
import Definitions.Def_actuarial_finiteEntropicPolicyValue
import Definitions.Def_actuarial_finiteEntropicStageCost

namespace ActuarialValuation

theorem finiteEntropicPolicyValue_succ {S A : Type*}
  [Fintype S] (P : S → A → S → ℝ)
  (cost : S → A → S → ℝ) (beta gamma : ℝ)
  (terminal : S → ℝ) (policy : ℕ → S → A) (n : ℕ) (s : S) :
  finiteEntropicPolicyValue P cost beta gamma terminal policy (n + 1) s =
    finiteEntropicStageCost P cost beta gamma
      (finiteEntropicPolicyValue P cost beta gamma terminal policy n)
      s (policy n s) := by sorry

end ActuarialValuation
