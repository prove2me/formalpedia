-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicBellmanMinimum_le
-- name    : ActuarialValuation.finiteEntropicBellmanMinimum_le
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:42:52.425504+00:00
-- url     : https://prove2.me/theorems/852cd367-605b-4e8b-91c3-df977bd56b07
-- title:
--   Optimal finite action cost does not exceed any chosen action
-- statement:
--   Regardless of stochastic-row or monotonicity assumptions, the finite-action minimum cannot exceed the value of any individual action. This is a direct order property of the finite nonempty action menu and supports the policy comparison induction used later.
--
--   **Mathematical statement**
--
--   $$
--   \min_{a'\in A}Q(s,a')\le Q(s,a)
--   $$
-- source:
--   Bäuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), Definition 4.6, Theorem 4.7, equation (4.2), DOI https://doi.org/10.1016/j.ejor.2021.04.030; Bäuerle and Jaśkiewicz (2024), entropic certainty equivalent, Example 1(a), equation (2), DOI https://doi.org/10.1007/s00186-024-00857-0; derived finite-state discrete-time insurer cost specialisation

import Mathlib
import Definitions.Def_actuarial_finiteEntropicBellmanMinimum
import Definitions.Def_actuarial_finiteEntropicStageCost

namespace ActuarialValuation

theorem finiteEntropicBellmanMinimum_le {S A : Type*}
  [Fintype S] [Fintype A] [Nonempty A]
  (P : S → A → S → ℝ) (cost : S → A → S → ℝ)
  (beta gamma : ℝ) (next : S → ℝ) (s : S) (a : A) :
  finiteEntropicBellmanMinimum P cost beta gamma next s ≤
    finiteEntropicStageCost P cost beta gamma next s a := by sorry

end ActuarialValuation
