-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_rejection_real_accepted_mass
-- name    : AppliedSDE.SarkkaSolin.rejection_real_accepted_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:47:00.959796+00:00
-- url     : https://prove2.me/theorems/65b77328-b8f3-407a-9c53-9ab08df5234d
-- title:
--   Real accepted mass equals integral of acceptance weight
-- statement:
--   Supporting theorem for exact rejection sampling in Sarkka and Solin (2019), Chapter 8; required by AppliedSDE.SarkkaSolin.exact_rejection_sampling_accepted_law.
-- source:
--   Sarkka and Solin (2019), Algorithm 8.23. Parent theorem abc82f18-47fe-43a7-853c-18d275099080.

import Mathlib
open MeasureTheory

theorem AppliedSDE.SarkkaSolin.rejection_real_accepted_mass
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (weight : Ω -> ℝ) (hweight : Measurable weight)
    (hbound : ∀ omega : Ω, 0 ≤ weight omega ∧ weight omega ≤ 1)
    (B : Set Ω) (hB : MeasurableSet B) :
    let U : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc 0 1)
    let C : Set (Ω × ℝ) := {z | z.2 ≤ weight z.1}
    ((P.prod U).restrict C).real (B ×ˢ Set.univ) =
      ∫ omega in B, weight omega ∂ P := by
  sorry
