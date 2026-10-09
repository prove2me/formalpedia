-- Prove2me | Theorems.Thm_ActuarialValuation_finiteHorizonMarkovOptimalPolicy_fundamental
-- name    : ActuarialValuation.finiteHorizonMarkovOptimalPolicy_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T07:20:27.589406+00:00
-- url     : https://prove2.me/theorems/89417c52-e95b-48c8-9daa-6e413ed9c0f8
-- title:
--   Optimal deterministic finite-horizon Markov policy capstone
-- statement:
--   Bellman value dominates every deterministic Markov policy and a deterministic remaining-horizon policy attains that value for all states.
--
--   **Mathematical statement**
--
--   $$
--   \forall\pi:V_n^\pi\le V_n,\quad\exists\pi^\star:V_n^{\pi^\star}=V_n
--   $$
-- source:
--   Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman optimality and finite-state/action deterministic Markov optimal policies, https://doi.org/10.1002/9780470316887.ch4; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048, motivational context only, not continuous-time verification

import Mathlib
import Definitions.Def_actuarial_finiteHorizonBellmanValue
import Definitions.Def_actuarial_finiteHorizonPolicyValue
open MeasureTheory

namespace ActuarialValuation

theorem finiteHorizonMarkovOptimalPolicy_fundamental {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (terminal : S → ℝ) (hP : ∀ s a t, 0 ≤ P s a t) (hv : 0 ≤ v) (n : ℕ)
  :
  ((∀ policy : ℕ → S → A, ∀ s : S,
  finiteHorizonPolicyValue P reward v terminal policy n s ≤
    finiteHorizonBellmanValue P reward v terminal n s)
  ∧ (∃ policy : ℕ → S → A, ∀ s : S,
  finiteHorizonPolicyValue P reward v terminal policy n s =
    finiteHorizonBellmanValue P reward v terminal n s)) := by sorry

end ActuarialValuation
