-- Prove2me | Theorems.Thm_ActuarialValuation_xlRetainedLeRetention
-- name    : ActuarialValuation.xlRetainedLeRetention
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:00:46.00402+00:00
-- url     : https://prove2.me/theorems/428dc9d2-2380-4309-a8d0-f43aa5cc9ff5
-- title:
--   Retained claim is capped by retention
-- statement:
--   The contractual threshold limits the insurer's part of the gross claim.
--
--   **Mathematical statement**
--
--   $$
--   r(z,a)\le a
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
import Definitions.Def_actuarial_xlRetainedLoss
open MeasureTheory

namespace ActuarialValuation

theorem xlRetainedLeRetention (z a : ℝ)
  :
  xlRetainedLoss z a ≤ a := by sorry

end ActuarialValuation
