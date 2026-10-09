-- Prove2me | Theorems.Thm_ActuarialValuation_finiteStageActionReturn_zero_discount
-- name    : ActuarialValuation.finiteStageActionReturn_zero_discount
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T07:09:07.101008+00:00
-- url     : https://prove2.me/theorems/120e58ad-8ecd-4beb-948a-4501bf3e87ca
-- title:
--   Zero discount leaves stage reward
-- statement:
--   When discount is zero, all future continuation contributions vanish.
--
--   **Mathematical statement**
--
--   $$
--   Q(s,a;U)|_{v=0}=r(s,a)
--   $$
-- source:
--   Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman optimality and finite-state/action deterministic Markov optimal policies, https://doi.org/10.1002/9780470316887.ch4; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048, motivational context only, not continuous-time verification

import Mathlib
import Definitions.Def_actuarial_finiteStageActionReturn
open MeasureTheory

namespace ActuarialValuation

theorem finiteStageActionReturn_zero_discount {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (next : S → ℝ) (s : S) (a : A)
  :
  finiteStageActionReturn P reward 0 next s a = reward s a := by sorry

end ActuarialValuation
