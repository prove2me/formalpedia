-- Prove2me | Theorems.Thm_ActuarialValuation_finiteStageBellmanMaximum_dominates
-- name    : ActuarialValuation.finiteStageBellmanMaximum_dominates
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T07:09:47.720297+00:00
-- url     : https://prove2.me/theorems/1e51c270-72c9-4962-87d0-53898b37ce35
-- title:
--   Bellman maximum dominates each action
-- statement:
--   The best finite action return is at least the return of any individual action.
--
--   **Mathematical statement**
--
--   $$
--   Q(s,a;U)\le TU(s)
--   $$
-- source:
--   Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman optimality and finite-state/action deterministic Markov optimal policies, https://doi.org/10.1002/9780470316887.ch4; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048, motivational context only, not continuous-time verification

import Mathlib
import Definitions.Def_actuarial_finiteStageActionReturn
import Definitions.Def_actuarial_finiteStageBellmanMaximum
open MeasureTheory

namespace ActuarialValuation

theorem finiteStageBellmanMaximum_dominates {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (next : S → ℝ) (s : S) (a : A)
  :
  finiteStageActionReturn P reward v next s a ≤
  finiteStageBellmanMaximum P reward v next s := by sorry

end ActuarialValuation
