-- Prove2me | Theorems.Thm_ActuarialValuation_xlExpectedCostAntitone
-- name    : ActuarialValuation.xlExpectedCostAntitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:12:13.838433+00:00
-- url     : https://prove2.me/theorems/7b535af9-b4d2-4afa-9909-12b1efcdd286
-- title:
--   Nonnegative reinsurance loading rewards higher retention in pure expected cost
-- statement:
--   With nonnegative claim scenario weights and safety loading, higher retention transfers less loaded ceded risk and reduces or preserves pure expected cost.
--
--   **Mathematical statement**
--
--   $$
--   a\le b,\theta\ge0\Rightarrow C_\theta(b)\le C_\theta(a)
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
import Definitions.Def_actuarial_xlExpectedValuePremiumCost
open MeasureTheory

namespace ActuarialValuation

theorem xlExpectedCostAntitone {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (a b θ : ℝ)
  (hw : ∀ ω, 0 ≤ w ω) (hθ : 0 ≤ θ) (hab : a ≤ b)
  :
  xlExpectedValuePremiumCost w z b θ ≤ xlExpectedValuePremiumCost w z a θ := by sorry

end ActuarialValuation
