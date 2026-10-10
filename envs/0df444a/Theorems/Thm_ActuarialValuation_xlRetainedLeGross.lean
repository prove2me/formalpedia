-- Prove2me | Theorems.Thm_ActuarialValuation_xlRetainedLeGross
-- name    : ActuarialValuation.xlRetainedLeGross
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:00:15.11113+00:00
-- url     : https://prove2.me/theorems/1a239f37-29dd-4511-b9c1-9ebbfa74b9d2
-- title:
--   Retained claim is capped by gross claim
-- statement:
--   The insurer retains no more than the entire gross claim.
--
--   **Mathematical statement**
--
--   $$
--   r(z,a)\le z
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
import Definitions.Def_actuarial_xlRetainedLoss
open MeasureTheory

namespace ActuarialValuation

theorem xlRetainedLeGross (z a : ℝ)
  :
  xlRetainedLoss z a ≤ z := by sorry

end ActuarialValuation
