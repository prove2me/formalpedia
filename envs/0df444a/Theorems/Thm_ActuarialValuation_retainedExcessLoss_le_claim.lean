-- Prove2me | Theorems.Thm_ActuarialValuation_retainedExcessLoss_le_claim
-- name    : ActuarialValuation.retainedExcessLoss_le_claim
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T06:08:57.09815+00:00
-- url     : https://prove2.me/theorems/65f48764-ac1b-4af3-bcc6-eee299f2b5d9
-- title:
--   Retained loss does not exceed gross claim
-- statement:
--   Minimum of retention and claim cannot exceed the claim amount.
--
--   **Mathematical statement**
--
--   $$
--   r(z,a)\le z
--   $$
-- source:
--   Brachetta and Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, Risks 7(2) 48, DOI https://doi.org/10.3390/risks7020048, §2 retained loss min(z,alpha), §3 HJB optimisation; Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman/backward induction, https://doi.org/10.1002/9780470316887.ch4

import Mathlib
import Definitions.Def_actuarial_retainedExcessLoss
open MeasureTheory

namespace ActuarialValuation

theorem retainedExcessLoss_le_claim (z a : ℝ)
  :
  retainedExcessLoss z a ≤ z := by sorry

end ActuarialValuation
