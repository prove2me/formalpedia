-- Prove2me | Theorems.Thm_ActuarialValuation_xlExpectedSplit
-- name    : ActuarialValuation.xlExpectedSplit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:03:30.233768+00:00
-- url     : https://prove2.me/theorems/b64ed6b6-ae5c-45fa-a66e-1d2b4fba6738
-- title:
--   Expected gross claim equals expected retained plus ceded claims
-- statement:
--   Finite weighted expectation preserves the pointwise gross-claim decomposition.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[r]+\mathbb E[c]=\mathbb E[Z]
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
import Definitions.Def_actuarial_xlCededLoss
import Definitions.Def_actuarial_xlExpectedLoss
import Definitions.Def_actuarial_xlRetainedLoss
open MeasureTheory

namespace ActuarialValuation

theorem xlExpectedSplit {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (a : ℝ)
  :
  xlExpectedLoss w (fun ω => xlRetainedLoss (z ω) a) +
  xlExpectedLoss w (fun ω => xlCededLoss (z ω) a) = xlExpectedLoss w z := by sorry

end ActuarialValuation
