-- Prove2me | Theorems.Thm_ActuarialValuation_expectedRetainedLoss_nonnegative
-- name    : ActuarialValuation.expectedRetainedLoss_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T06:19:15.552287+00:00
-- url     : https://prove2.me/theorems/d7645d66-2aa2-4409-a201-4dbcdab34ee5
-- title:
--   Nonnegative claims produce nonnegative expected retained losses
-- statement:
--   Finite weighted sum of nonnegative retention payments is nonnegative.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[r(Z,a)]\ge0
--   $$
-- source:
--   Brachetta and Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, Risks 7(2) 48, DOI https://doi.org/10.3390/risks7020048, §2 retained loss min(z,alpha), §3 HJB optimisation; Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman/backward induction, https://doi.org/10.1002/9780470316887.ch4

import Mathlib
import Definitions.Def_actuarial_expectedRetainedLoss
open MeasureTheory

namespace ActuarialValuation

theorem expectedRetainedLoss_nonnegative {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (a : ℝ)
  (hw : ∀ ω, 0 ≤ w ω) (hz : ∀ ω, 0 ≤ z ω) (ha : 0 ≤ a)
  :
  0 ≤ expectedRetainedLoss w z a := by sorry

end ActuarialValuation
