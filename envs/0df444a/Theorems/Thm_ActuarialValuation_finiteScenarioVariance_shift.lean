-- Prove2me | Theorems.Thm_ActuarialValuation_finiteScenarioVariance_shift
-- name    : ActuarialValuation.finiteScenarioVariance_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T06:14:56.250631+00:00
-- url     : https://prove2.me/theorems/ee96f137-fc02-4bed-97d1-d9d2f6ee90e4
-- title:
--   Adding a deterministic reserve constant leaves variance unchanged
-- statement:
--   A constant reserve translation changes mean but not scenario variance when weights total one.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}(X+a)=\operatorname{Var}(X)
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
import Definitions.Def_actuarial_finiteScenarioVariance
open MeasureTheory

namespace ActuarialValuation

theorem finiteScenarioVariance_shift {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (X : Ω → ℝ) (a : ℝ)
  (hw : (∑ ω : Ω, w ω) = 1)
  :
  finiteScenarioVariance w (fun ω => X ω + a) = finiteScenarioVariance w X := by sorry

end ActuarialValuation
