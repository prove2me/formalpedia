-- Prove2me | Theorems.Thm_ActuarialValuation_xlRetainedVarianceNonnegative
-- name    : ActuarialValuation.xlRetainedVarianceNonnegative
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:14:25.321245+00:00
-- url     : https://prove2.me/theorems/5887b7cb-fcb3-4832-90a6-c8d733550630
-- title:
--   Retained-claim variance is nonnegative
-- statement:
--   Nonnegative scenario weights multiply squared centred retained claims, giving nonnegative variance charge.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}_w[r(Z,a)]\ge0
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
import Definitions.Def_actuarial_xlRetainedVariance
open MeasureTheory

namespace ActuarialValuation

theorem xlRetainedVarianceNonnegative {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (a : ℝ) (hw : ∀ ω, 0 ≤ w ω)
  :
  0 ≤ xlRetainedVariance w z a := by sorry

end ActuarialValuation
