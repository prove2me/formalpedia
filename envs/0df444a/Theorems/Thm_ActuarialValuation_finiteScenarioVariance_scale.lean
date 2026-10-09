-- Prove2me | Theorems.Thm_ActuarialValuation_finiteScenarioVariance_scale
-- name    : ActuarialValuation.finiteScenarioVariance_scale
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T06:13:45.911697+00:00
-- url     : https://prove2.me/theorems/1eb54000-00f4-475b-8dd2-beb20768edd3
-- title:
--   Variance scales quadratically
-- statement:
--   Scaling monetary losses by a multiplies variance by a squared.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}(aX)=a^2\operatorname{Var}(X)
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
import Definitions.Def_actuarial_finiteScenarioVariance
open MeasureTheory

namespace ActuarialValuation

theorem finiteScenarioVariance_scale {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (X : Ω → ℝ) (a : ℝ)
  :
  finiteScenarioVariance w (fun ω => a * X ω) = a ^ 2 * finiteScenarioVariance w X := by sorry

end ActuarialValuation
