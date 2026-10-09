-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicBellmanValue_succ
-- name    : ActuarialValuation.finiteEntropicBellmanValue_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:48:07.184458+00:00
-- url     : https://prove2.me/theorems/b8b4a69b-0884-4f8a-926c-91cea2e89c19
-- title:
--   An additional horizon year minimises conditional entropic cost
-- statement:
--   The next step in the remaining-horizon optimal cost sequence is obtained by minimising the conditional entropic value of each current action using the previous Bellman value as continuation. This is the finite-state, cost-minimising form of recursive risk-sensitive dynamic programming.
--
--   **Mathematical statement**
--
--   $$
--   V_{n+1}(s)=\min_{a\in A}Q_{\gamma,\beta}(s,a;V_n)
--   $$
-- source:
--   Bäuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), Definition 4.6, Theorem 4.7, equation (4.2), DOI https://doi.org/10.1016/j.ejor.2021.04.030; Bäuerle and Jaśkiewicz (2024), entropic certainty equivalent, Example 1(a), equation (2), DOI https://doi.org/10.1007/s00186-024-00857-0; derived finite-state discrete-time insurer cost specialisation

import Mathlib
import Definitions.Def_actuarial_finiteEntropicBellmanValue
import Definitions.Def_actuarial_finiteEntropicBellmanMinimum

namespace ActuarialValuation

theorem finiteEntropicBellmanValue_succ {S A : Type*}
  [Fintype S] [Fintype A] [Nonempty A]
  (P : S → A → S → ℝ)
  (cost : S → A → S → ℝ) (beta gamma : ℝ)
  (terminal : S → ℝ) (n : ℕ) (s : S) :
  finiteEntropicBellmanValue P cost beta gamma terminal (n + 1) s =
    finiteEntropicBellmanMinimum P cost beta gamma
      (finiteEntropicBellmanValue P cost beta gamma terminal n) s := by sorry

end ActuarialValuation
