-- Prove2me | Theorems.Thm_ActuarialValuation_finiteHorizonBellmanValue_zero
-- name    : ActuarialValuation.finiteHorizonBellmanValue_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T07:15:11.467826+00:00
-- url     : https://prove2.me/theorems/da055a10-4681-48ad-a7bb-727609de7f84
-- title:
--   Bellman value at zero horizon
-- statement:
--   Zero remaining actions reduce Bellman value to the terminal state payoff.
--
--   **Mathematical statement**
--
--   $$
--   V_0(s)=h(s)
--   $$
-- source:
--   Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman optimality and finite-state/action deterministic Markov optimal policies, https://doi.org/10.1002/9780470316887.ch4; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048, motivational context only, not continuous-time verification

import Mathlib
import Definitions.Def_actuarial_finiteHorizonBellmanValue
open MeasureTheory

namespace ActuarialValuation

theorem finiteHorizonBellmanValue_zero {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (terminal : S → ℝ) (s : S)
  :
  finiteHorizonBellmanValue P reward v terminal 0 s = terminal s := by sorry

end ActuarialValuation
