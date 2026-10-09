-- Prove2me | Theorems.Thm_ActuarialValuation_deathYearEvent_measurable
-- name    : ActuarialValuation.deathYearEvent_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T17:42:05.696861+00:00
-- url     : https://prove2.me/theorems/89c45962-068e-41e6-b67b-ffa618c03ed4
-- title:
--   Death-year events are measurable
-- statement:
--   Show that measurability of the curtate lifetime makes the event of death in each policy year measurable.
--
--   **Mathematical statement**
--
--   $$
--   D_k\in\mathcal F
--   $$
-- source:
--   Chapter 2 §2.4.3, https://openacttextdev.github.io/LifeCon/C-ModelingLifeTimes.html; measurable random variable reformulation.

import Mathlib
import Definitions.Def_actuarial_deathYearEvent
open MeasureTheory

namespace ActuarialValuation
theorem deathYearEvent_measurable {Ω : Type*} [MeasurableSpace Ω]
    (K : Ω → ℕ) (hK : Measurable K)
    (k : ℕ)
    :
    MeasurableSet (deathYearEvent K k) := by sorry
end ActuarialValuation
