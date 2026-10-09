-- Prove2me | Theorems.Thm_ActuarialValuation_valuationSurvivalEvent_measurable
-- name    : ActuarialValuation.valuationSurvivalEvent_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:41:14.71157+00:00
-- url     : https://prove2.me/theorems/afe6fdc1-1091-42e3-b5c9-bb2fecde0db6
-- title:
--   In-force event is measurable
-- statement:
--   Survival to a fixed duration is a measurable event.
--
--   **Mathematical statement**
--
--   $$
--   S_t\in\mathcal F
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
import Definitions.Def_actuarial_valuationSurvivalEvent
open MeasureTheory

namespace ActuarialValuation

theorem valuationSurvivalEvent_measurable {Ω : Type*} [MeasurableSpace Ω] (K : Ω → ℕ) (hK : Measurable K) (t : ℕ)
    :
    MeasurableSet (valuationSurvivalEvent K t) := by sorry

end ActuarialValuation
