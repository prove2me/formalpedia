-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_discrete_stopping_region_predictable
-- name    : AvramDividend.Classical.avram_wave4_p1_discrete_stopping_region_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:53:37.445406+00:00
-- url     : https://prove2.me/theorems/a13f2201-627d-4366-9cb4-4d7079f6c0f0
-- title:
--   Discrete stopping-time survival region is predictable, with endpoint included
-- statement:
--   For a stopping time with values in WithTop Nat on a genuinely filtered measurable space, the entire set of time-path pairs (n,omega) with n at or before the stopping index is measurable in the filtration's predictable sigma-algebra. Its complement is the countable union of predictable generating rectangles (k,infinity) times the event that the stopping time is at most k. This derives stopped predictability from the stopping-time property without assuming a stopped compensation identity.
-- source:
--   Pinned Mathlib Probability/Process/Predictable.lean Filtration.predictable and measurableSet_predictable_Ioi_prod, Probability/Process/Stopping.lean IsStoppingTime. Applebaum, Levy Processes and Stochastic Calculus 2nd ed., predictable stopping.

import Mathlib

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_discrete_stopping_region_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℕ mΩ)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime 𝓕 τ) :
    MeasurableSet[𝓕.predictable]
      {p : ℕ × Ω | (p.1 : WithTop ℕ) ≤ τ p.2} := by sorry
