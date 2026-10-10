-- Prove2me | Theorems.Thm_ActuarialValuation_finiteScenarioVariance_zero
-- name    : ActuarialValuation.finiteScenarioVariance_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T06:11:22.647714+00:00
-- url     : https://prove2.me/theorems/778cd726-88d2-4e3c-9e00-0d287f63c5ae
-- title:
--   Zero gain has zero variance
-- statement:
--   All zero scenario values coincide with their expected value.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}(0)=0
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
import Definitions.Def_actuarial_finiteScenarioVariance
open MeasureTheory

namespace ActuarialValuation

theorem finiteScenarioVariance_zero {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
  :
  finiteScenarioVariance w (fun _ => 0) = 0 := by sorry

end ActuarialValuation
