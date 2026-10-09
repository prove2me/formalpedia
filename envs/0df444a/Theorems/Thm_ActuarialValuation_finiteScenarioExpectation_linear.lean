-- Prove2me | Theorems.Thm_ActuarialValuation_finiteScenarioExpectation_linear
-- name    : ActuarialValuation.finiteScenarioExpectation_linear
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T23:26:03.96997+00:00
-- url     : https://prove2.me/theorems/5d3fc50b-e246-4552-a56b-7458d3b7c716
-- title:
--   Weighted expectation is linear
-- statement:
--   Linearity holds for finite weighted sums irrespective of correlations.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[X+aY]=\mathbb E[X]+a\mathbb E[Y]
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
import Definitions.Def_actuarial_finiteScenarioExpectation
open MeasureTheory

namespace ActuarialValuation

theorem finiteScenarioExpectation_linear {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (X Y : Ω → ℝ) (a : ℝ)
  :
  finiteScenarioExpectation w (fun ω => X ω + a * Y ω) =
    finiteScenarioExpectation w X + a * finiteScenarioExpectation w Y := by sorry

end ActuarialValuation
