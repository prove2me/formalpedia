-- Prove2me | Theorems.Thm_ActuarialValuation_excessLoss_split
-- name    : ActuarialValuation.excessLoss_split
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T06:15:39.82577+00:00
-- url     : https://prove2.me/theorems/6bc582ad-21c9-4e99-98e1-c830197812c9
-- title:
--   Gross claim divides into retained and ceded losses
-- statement:
--   Every claim is partitioned exactly between the cedant and the reinsurer.
--
--   **Mathematical statement**
--
--   $$
--   r(z,a)+c(z,a)=z
--   $$
-- source:
--   Brachetta and Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, Risks 7(2) 48, DOI https://doi.org/10.3390/risks7020048, §2 retained loss min(z,alpha), §3 HJB optimisation; Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman/backward induction, https://doi.org/10.1002/9780470316887.ch4

import Mathlib
import Definitions.Def_actuarial_cededExcessLoss
import Definitions.Def_actuarial_retainedExcessLoss
open MeasureTheory

namespace ActuarialValuation

theorem excessLoss_split (z a : ℝ)
  :
  retainedExcessLoss z a + cededExcessLoss z a = z := by sorry

end ActuarialValuation
