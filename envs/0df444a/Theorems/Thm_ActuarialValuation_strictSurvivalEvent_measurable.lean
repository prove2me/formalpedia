-- Prove2me | Theorems.Thm_ActuarialValuation_strictSurvivalEvent_measurable
-- name    : ActuarialValuation.strictSurvivalEvent_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T19:15:24.326993+00:00
-- url     : https://prove2.me/theorems/894c21f7-5f9c-46aa-b383-30309db312e1
-- title:
--   Strict survival event is measurable
-- statement:
--   The event that exact lifetime exceeds the term is measurable, provided exact lifetime is a measurable random variable.
--
--   **Mathematical statement**
--
--   $$
--   T\text{ measurable}\implies E_n^>\in\mathcal F
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.2.3, equation (3.9), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_strictSurvivalEvent
open MeasureTheory

namespace ActuarialValuation

theorem strictSurvivalEvent_measurable {Ω : Type*} [MeasurableSpace Ω] (T : Ω → ℝ) (hT : Measurable T) (n : ℕ)
    : MeasurableSet (strictSurvivalEvent T n) := by sorry

end ActuarialValuation
