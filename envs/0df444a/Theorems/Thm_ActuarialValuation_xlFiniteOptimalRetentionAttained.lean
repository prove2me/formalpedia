-- Prove2me | Theorems.Thm_ActuarialValuation_xlFiniteOptimalRetentionAttained
-- name    : ActuarialValuation.xlFiniteOptimalRetentionAttained
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:18:59.95963+00:00
-- url     : https://prove2.me/theorems/8da6e191-7e68-4d70-b137-f2bbf7fd113d
-- title:
--   Finite menu has an attaining retention
-- statement:
--   The nonempty finite action menu admits a retention attaining the minimum risk-adjusted cost.
--
--   **Mathematical statement**
--
--   $$
--   \exists a^\star,\ J^\star=J(\alpha_{a^\star})
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
import Definitions.Def_actuarial_xlFiniteOptimalRetentionCost
import Definitions.Def_actuarial_xlRiskAdjustedRetentionCost
open MeasureTheory

namespace ActuarialValuation

theorem xlFiniteOptimalRetentionAttained {Ω A : Type*} [Fintype Ω] [Fintype A] [Nonempty A] (w z : Ω → ℝ) (retention : A → ℝ) (θ kap : ℝ)
  :
  ∃ a : A, xlFiniteOptimalRetentionCost w z retention θ kap =
   xlRiskAdjustedRetentionCost w z θ kap (retention a) := by sorry

end ActuarialValuation
