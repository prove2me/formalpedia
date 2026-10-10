-- Prove2me | Theorems.Thm_ActuarialValuation_finiteHorizonBellmanValue_succ
-- name    : ActuarialValuation.finiteHorizonBellmanValue_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T07:17:29.413158+00:00
-- url     : https://prove2.me/theorems/1cbb15f5-d290-408b-8a3f-d5ca91fd0e7a
-- title:
--   Bellman value recursion
-- statement:
--   Backward induction evaluates best current action assuming optimal continuation.
--
--   **Mathematical statement**
--
--   $$
--   V_{n+1}=TV_n
--   $$
-- source:
--   Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman optimality and finite-state/action deterministic Markov optimal policies, https://doi.org/10.1002/9780470316887.ch4; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048, motivational context only, not continuous-time verification

import Mathlib
import Definitions.Def_actuarial_finiteHorizonBellmanValue
import Definitions.Def_actuarial_finiteStageBellmanMaximum
open MeasureTheory

namespace ActuarialValuation

theorem finiteHorizonBellmanValue_succ {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (terminal : S → ℝ) (n : ℕ) (s : S)
  :
  finiteHorizonBellmanValue P reward v terminal (n + 1) s =
  finiteStageBellmanMaximum P reward v
    (finiteHorizonBellmanValue P reward v terminal n) s := by sorry

end ActuarialValuation
