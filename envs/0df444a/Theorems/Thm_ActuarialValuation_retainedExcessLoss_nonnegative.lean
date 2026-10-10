-- Prove2me | Theorems.Thm_ActuarialValuation_retainedExcessLoss_nonnegative
-- name    : ActuarialValuation.retainedExcessLoss_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T06:13:54.987019+00:00
-- url     : https://prove2.me/theorems/d00004c6-eb95-4bed-be7b-c4bed6afd639
-- title:
--   Retained loss is nonnegative for nonnegative inputs
-- statement:
--   The minimum of two nonnegative monetary amounts is nonnegative.
--
--   **Mathematical statement**
--
--   $$
--   z,a\ge0\implies r(z,a)\ge0
--   $$
-- source:
--   Brachetta and Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, Risks 7(2) 48, DOI https://doi.org/10.3390/risks7020048, §2 retained loss min(z,alpha), §3 HJB optimisation; Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman/backward induction, https://doi.org/10.1002/9780470316887.ch4

import Mathlib
import Definitions.Def_actuarial_retainedExcessLoss
open MeasureTheory

namespace ActuarialValuation

theorem retainedExcessLoss_nonnegative (z a : ℝ) (hz : 0 ≤ z) (ha : 0 ≤ a)
  :
  0 ≤ retainedExcessLoss z a := by sorry

end ActuarialValuation
