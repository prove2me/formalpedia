-- Prove2me | Theorems.Thm_ActuarialValuation_xlRetainedPlusCeded
-- name    : ActuarialValuation.xlRetainedPlusCeded
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T08:59:46.774781+00:00
-- url     : https://prove2.me/theorems/cb669a04-ab6e-4981-b072-8e72fdfaf4c5
-- title:
--   Gross claim divides between cedant and reinsurer
-- statement:
--   The retained and ceded losses add exactly to the realised gross claim.
--
--   **Mathematical statement**
--
--   $$
--   r(z,a)+c(z,a)=z
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
import Definitions.Def_actuarial_xlCededLoss
import Definitions.Def_actuarial_xlRetainedLoss
open MeasureTheory

namespace ActuarialValuation

theorem xlRetainedPlusCeded (z a : ℝ)
  :
  xlRetainedLoss z a + xlCededLoss z a = z := by sorry

end ActuarialValuation
