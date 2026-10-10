-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicBellmanMinimum_attained
-- name    : ActuarialValuation.finiteEntropicBellmanMinimum_attained
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:44:03.392633+00:00
-- url     : https://prove2.me/theorems/6a9f75f4-965b-440f-bc05-619e12e1a967
-- title:
--   Some action achieves the finite entropic Bellman minimum
-- statement:
--   For every current state and fixed continuation value, a finite nonempty action set has an attaining minimiser. This claim relies on the finite order-completeness of the action list, not on a continuous-action compactness theorem. It is the local selector required to construct an optimal deterministic nonstationary Markov policy.
--
--   **Mathematical statement**
--
--   $$
--   \exists a^*\in A,\ Q(s,a^*)=\min_{a\in A}Q(s,a)
--   $$
-- source:
--   Bäuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), Definition 4.6, Theorem 4.7, equation (4.2), DOI https://doi.org/10.1016/j.ejor.2021.04.030; Bäuerle and Jaśkiewicz (2024), entropic certainty equivalent, Example 1(a), equation (2), DOI https://doi.org/10.1007/s00186-024-00857-0; derived finite-state discrete-time insurer cost specialisation

import Mathlib
import Definitions.Def_actuarial_finiteEntropicBellmanMinimum
import Definitions.Def_actuarial_finiteEntropicStageCost

namespace ActuarialValuation

theorem finiteEntropicBellmanMinimum_attained {S A : Type*}
  [Fintype S] [Fintype A] [Nonempty A]
  (P : S → A → S → ℝ) (cost : S → A → S → ℝ)
  (beta gamma : ℝ) (next : S → ℝ) (s : S) :
  ∃ a : A, finiteEntropicStageCost P cost beta gamma next s a =
    finiteEntropicBellmanMinimum P cost beta gamma next s := by sorry

end ActuarialValuation
