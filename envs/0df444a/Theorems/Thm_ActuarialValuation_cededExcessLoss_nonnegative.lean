-- Prove2me | Theorems.Thm_ActuarialValuation_cededExcessLoss_nonnegative
-- name    : ActuarialValuation.cededExcessLoss_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T06:14:25.599517+00:00
-- url     : https://prove2.me/theorems/85e71699-1ea6-4267-b02a-da5909e0458c
-- title:
--   Ceded claim amount is nonnegative
-- statement:
--   The ceded claim equals z minus a number no larger than z, so is nonnegative for every real inputs.
--
--   **Mathematical statement**
--
--   $$
--   c(z,a)\ge0
--   $$
-- source:
--   Brachetta and Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, Risks 7(2) 48, DOI https://doi.org/10.3390/risks7020048, §2 retained loss min(z,alpha), §3 HJB optimisation; Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman/backward induction, https://doi.org/10.1002/9780470316887.ch4

import Mathlib
import Definitions.Def_actuarial_cededExcessLoss
open MeasureTheory

namespace ActuarialValuation

theorem cededExcessLoss_nonnegative (z a : ℝ)
  :
  0 ≤ cededExcessLoss z a := by sorry

end ActuarialValuation
