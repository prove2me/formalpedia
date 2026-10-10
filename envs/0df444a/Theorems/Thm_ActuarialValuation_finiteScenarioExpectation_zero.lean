-- Prove2me | Theorems.Thm_ActuarialValuation_finiteScenarioExpectation_zero
-- name    : ActuarialValuation.finiteScenarioExpectation_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:22:20.88516+00:00
-- url     : https://prove2.me/theorems/e426198c-430c-48ee-a1ad-7cb8d563834b
-- title:
--   Zero cashflow has zero expected value
-- statement:
--   Zero in every scenario implies zero weighted expectation.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E_w[0]=0
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
import Definitions.Def_actuarial_finiteScenarioExpectation
open MeasureTheory

namespace ActuarialValuation

theorem finiteScenarioExpectation_zero {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
  :
  finiteScenarioExpectation w (fun _ => 0) = 0 := by sorry

end ActuarialValuation
