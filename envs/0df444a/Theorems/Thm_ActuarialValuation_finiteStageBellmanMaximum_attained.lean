-- Prove2me | Theorems.Thm_ActuarialValuation_finiteStageBellmanMaximum_attained
-- name    : ActuarialValuation.finiteStageBellmanMaximum_attained
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T07:10:20.32253+00:00
-- url     : https://prove2.me/theorems/4495ba05-376e-4224-a605-0e9bee88c81c
-- title:
--   Bellman maximum attained by an admissible action
-- statement:
--   Every real-valued function on a nonempty finite action type reaches its maximum.
--
--   **Mathematical statement**
--
--   $$
--   \exists a^\star,\ TU(s)=Q(s,a^\star;U)
--   $$
-- source:
--   Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman optimality and finite-state/action deterministic Markov optimal policies, https://doi.org/10.1002/9780470316887.ch4; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048, motivational context only, not continuous-time verification

import Mathlib
import Definitions.Def_actuarial_finiteStageActionReturn
import Definitions.Def_actuarial_finiteStageBellmanMaximum
open MeasureTheory

namespace ActuarialValuation

theorem finiteStageBellmanMaximum_attained {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (next : S → ℝ) (s : S)
  :
  ∃ a : A, finiteStageBellmanMaximum P reward v next s =
  finiteStageActionReturn P reward v next s a := by sorry

end ActuarialValuation
