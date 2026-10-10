-- Prove2me | Theorems.Thm_ActuarialValuation_finiteScenarioExpectation_const
-- name    : ActuarialValuation.finiteScenarioExpectation_const
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:24:20.182075+00:00
-- url     : https://prove2.me/theorems/0b28d571-0f41-46bf-afa0-9d9c8e3783d1
-- title:
--   Constant benefit has its face-value expectation
-- statement:
--   When scenario weights sum to one a constant cashflow has its full face value.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E_w[a]=a
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
import Definitions.Def_actuarial_finiteScenarioExpectation
open MeasureTheory

namespace ActuarialValuation

theorem finiteScenarioExpectation_const {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (hw : (∑ ω : Ω, w ω) = 1) (a : ℝ)
  :
  finiteScenarioExpectation w (fun _ => a) = a := by sorry

end ActuarialValuation
