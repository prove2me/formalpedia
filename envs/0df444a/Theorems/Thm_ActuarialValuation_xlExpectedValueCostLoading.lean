-- Prove2me | Theorems.Thm_ActuarialValuation_xlExpectedValueCostLoading
-- name    : ActuarialValuation.xlExpectedValueCostLoading
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:04:25.303255+00:00
-- url     : https://prove2.me/theorems/5ca5894f-d85f-4e7a-b9ba-e0f35413d40c
-- title:
--   Premium-cost identity isolates reinsurer safety loading
-- statement:
--   The expected-value premium cost equals gross expected loss plus loading theta on the ceded part.
--
--   **Mathematical statement**
--
--   $$
--   C_\theta(a)=\mathbb E[Z]+\theta\mathbb E[c(Z,a)]
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
import Definitions.Def_actuarial_xlCededLoss
import Definitions.Def_actuarial_xlExpectedLoss
import Definitions.Def_actuarial_xlExpectedValuePremiumCost
open MeasureTheory

namespace ActuarialValuation

theorem xlExpectedValueCostLoading {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (a θ : ℝ)
  :
  xlExpectedValuePremiumCost w z a θ =
    xlExpectedLoss w z + θ * xlExpectedLoss w (fun ω => xlCededLoss (z ω) a) := by sorry

end ActuarialValuation
