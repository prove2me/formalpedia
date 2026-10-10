-- Prove2me | Theorems.Thm_ActuarialValuation_finiteHorizonBellmanValue_policy_attains
-- name    : ActuarialValuation.finiteHorizonBellmanValue_policy_attains
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T07:18:51.277982+00:00
-- url     : https://prove2.me/theorems/d9cde55e-adbb-4375-92be-8ff191f8cd29
-- title:
--   Existence of an optimal nonstationary Markov policy
-- statement:
--   Finite argmax choices at each state and remaining horizon can be assembled into a deterministic policy attaining Bellman value.
--
--   **Mathematical statement**
--
--   $$
--   \exists\pi^\star,\ V_n^{\pi^\star}=V_n
--   $$
-- source:
--   Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman optimality and finite-state/action deterministic Markov optimal policies, https://doi.org/10.1002/9780470316887.ch4; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048, motivational context only, not continuous-time verification

import Mathlib
import Definitions.Def_actuarial_finiteHorizonBellmanValue
import Definitions.Def_actuarial_finiteHorizonPolicyValue
open MeasureTheory

namespace ActuarialValuation

theorem finiteHorizonBellmanValue_policy_attains {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (terminal : S → ℝ) (n : ℕ)
  :
  ∃ policy : ℕ → S → A, ∀ s : S,
  finiteHorizonPolicyValue P reward v terminal policy n s =
    finiteHorizonBellmanValue P reward v terminal n s := by sorry

end ActuarialValuation
