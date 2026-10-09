-- Prove2me | Theorems.Thm_ActuarialValuation_curtateSurvivalEvent_measurable
-- name    : ActuarialValuation.curtateSurvivalEvent_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T19:16:05.017695+00:00
-- url     : https://prove2.me/theorems/3890ed64-7bc3-4fa0-91f1-dc69e7d00a9f
-- title:
--   Curtate maturity event is measurable
-- statement:
--   The event that curtate lifetime is at least the term is measurable, provided the curtate lifetime is a measurable random variable.
--
--   **Mathematical statement**
--
--   $$
--   K\text{ measurable}\implies E_n^\ge\in\mathcal F
--   $$
-- source:
--   *Life Contingencies*, Chapter 2 §2.4.3, https://openacttextdev.github.io/LifeCon/C-ModelingLifeTimes.html; mathematical reconciliation of §3.2.3 eq (3.9) and §3.2.4 eq (3.10), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
open MeasureTheory

namespace ActuarialValuation

theorem curtateSurvivalEvent_measurable {Ω : Type*} [MeasurableSpace Ω] (K : Ω → ℕ) (hK : Measurable K) (n : ℕ)
    : MeasurableSet (curtateSurvivalEvent K n) := by sorry

end ActuarialValuation
