-- Prove2me | Theorems.Thm_ActuarialValuation_xlFiniteOptimalRetentionLowerBound
-- name    : ActuarialValuation.xlFiniteOptimalRetentionLowerBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:18:04.005495+00:00
-- url     : https://prove2.me/theorems/d272b065-0c57-4fea-bd11-24afabd07585
-- title:
--   Finite optimum is below every candidate cost
-- statement:
--   The minimum risk-adjusted retention cost is no greater than any admissible quoted retention's cost.
--
--   **Mathematical statement**
--
--   $$
--   J^\star\le J(\alpha_a)
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
import Definitions.Def_actuarial_xlFiniteOptimalRetentionCost
import Definitions.Def_actuarial_xlRiskAdjustedRetentionCost
open MeasureTheory

namespace ActuarialValuation

theorem xlFiniteOptimalRetentionLowerBound {Ω A : Type*} [Fintype Ω] [Fintype A] [Nonempty A] (w z : Ω → ℝ) (retention : A → ℝ) (θ kap : ℝ) (a : A)
  :
  xlFiniteOptimalRetentionCost w z retention θ kap ≤
    xlRiskAdjustedRetentionCost w z θ kap (retention a) := by sorry

end ActuarialValuation
