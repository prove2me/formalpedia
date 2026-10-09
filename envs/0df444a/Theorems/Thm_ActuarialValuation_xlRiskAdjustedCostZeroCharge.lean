-- Prove2me | Theorems.Thm_ActuarialValuation_xlRiskAdjustedCostZeroCharge
-- name    : ActuarialValuation.xlRiskAdjustedCostZeroCharge
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:17:19.51325+00:00
-- url     : https://prove2.me/theorems/01d4756f-3bdf-4f05-b5cd-6f85bc62764d
-- title:
--   Zero risk charge reduces to expected-value cost
-- statement:
--   Setting the risk-capital coefficient to zero removes retained claim variability cost entirely.
--
--   **Mathematical statement**
--
--   $$
--   J_{\theta,0}(a)=C_\theta(a)
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
import Definitions.Def_actuarial_xlExpectedValuePremiumCost
import Definitions.Def_actuarial_xlRiskAdjustedRetentionCost
open MeasureTheory

namespace ActuarialValuation

theorem xlRiskAdjustedCostZeroCharge {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (θ a : ℝ)
  :
  xlRiskAdjustedRetentionCost w z θ 0 a = xlExpectedValuePremiumCost w z a θ := by sorry

end ActuarialValuation
