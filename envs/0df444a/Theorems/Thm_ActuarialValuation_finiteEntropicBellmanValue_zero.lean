-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicBellmanValue_zero
-- name    : ActuarialValuation.finiteEntropicBellmanValue_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:47:11.351418+00:00
-- url     : https://prove2.me/theorems/bdea897a-b6d8-4b92-bc3b-9b22525a50cc
-- title:
--   Zero-year optimal entropic valuation equals terminal cost
-- statement:
--   At a zero-horizon valuation date, the optimiser cannot improve or worsen an immediate given terminal reserve or terminal insurance loss. The Bellman value is exactly that terminal amount, even if the state type is empty or the discount factor is zero.
--
--   **Mathematical statement**
--
--   $$
--   V_0(s)=h(s)
--   $$
-- source:
--   Bäuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), Definition 4.6, Theorem 4.7, equation (4.2), DOI https://doi.org/10.1016/j.ejor.2021.04.030; Bäuerle and Jaśkiewicz (2024), entropic certainty equivalent, Example 1(a), equation (2), DOI https://doi.org/10.1007/s00186-024-00857-0; derived finite-state discrete-time insurer cost specialisation

import Mathlib
import Definitions.Def_actuarial_finiteEntropicBellmanValue

namespace ActuarialValuation

theorem finiteEntropicBellmanValue_zero {S A : Type*}
  [Fintype S] [Fintype A] [Nonempty A]
  (P : S → A → S → ℝ)
  (cost : S → A → S → ℝ) (beta gamma : ℝ)
  (terminal : S → ℝ) (s : S) :
  finiteEntropicBellmanValue P cost beta gamma terminal 0 s =
    terminal s := by sorry

end ActuarialValuation
