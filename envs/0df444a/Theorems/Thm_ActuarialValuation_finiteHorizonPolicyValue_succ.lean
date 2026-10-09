-- Prove2me | Theorems.Thm_ActuarialValuation_finiteHorizonPolicyValue_succ
-- name    : ActuarialValuation.finiteHorizonPolicyValue_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T07:14:15.959668+00:00
-- url     : https://prove2.me/theorems/49dda38d-921b-4a7d-996e-7c3eea364a58
-- title:
--   Policy recursion for one additional stage
-- statement:
--   The action indexed by remaining horizon n is followed by the optimality-independent continuation for n stages.
--
--   **Mathematical statement**
--
--   $$
--   V^\pi_{n+1}=Q(s,\pi_n(s);V^\pi_n)
--   $$
-- source:
--   Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman optimality and finite-state/action deterministic Markov optimal policies, https://doi.org/10.1002/9780470316887.ch4; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048, motivational context only, not continuous-time verification

import Mathlib
import Definitions.Def_actuarial_finiteHorizonPolicyValue
import Definitions.Def_actuarial_finiteStageActionReturn
open MeasureTheory

namespace ActuarialValuation

theorem finiteHorizonPolicyValue_succ {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (terminal : S → ℝ) (policy : ℕ → S → A) (n : ℕ) (s : S)
  :
  finiteHorizonPolicyValue P reward v terminal policy (n + 1) s =
  finiteStageActionReturn P reward v
    (finiteHorizonPolicyValue P reward v terminal policy n) s (policy n s) := by sorry

end ActuarialValuation
