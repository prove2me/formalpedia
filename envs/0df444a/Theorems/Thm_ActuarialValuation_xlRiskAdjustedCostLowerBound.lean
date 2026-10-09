-- Prove2me | Theorems.Thm_ActuarialValuation_xlRiskAdjustedCostLowerBound
-- name    : ActuarialValuation.xlRiskAdjustedCostLowerBound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:16:25.839134+00:00
-- url     : https://prove2.me/theorems/8354aa56-019d-4794-b925-dd0beece36d5
-- title:
--   Nonnegative risk loading cannot decrease expected premium cost
-- statement:
--   Adding a nonnegative variance charge raises or preserves the expected-value cost.
--
--   **Mathematical statement**
--
--   $$
--   \lambda\ge0\Rightarrow J_{\theta,\lambda}(a)\ge C_\theta(a)
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
import Definitions.Def_actuarial_xlExpectedValuePremiumCost
import Definitions.Def_actuarial_xlRiskAdjustedRetentionCost
open MeasureTheory

namespace ActuarialValuation

theorem xlRiskAdjustedCostLowerBound {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (θ kap a : ℝ)
  (hw : ∀ ω, 0 ≤ w ω) (hkap : 0 ≤ kap)
  :
  xlExpectedValuePremiumCost w z a θ ≤ xlRiskAdjustedRetentionCost w z θ kap a := by sorry

end ActuarialValuation
