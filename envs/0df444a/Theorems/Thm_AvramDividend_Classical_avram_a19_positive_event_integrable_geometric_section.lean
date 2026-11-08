-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_positive_event_integrable_geometric_section
-- name    : AvramDividend.Classical.avram_a19_positive_event_integrable_geometric_section
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:08:39.808787+00:00
-- url     : https://prove2.me/theorems/245baf16-47a3-4d4d-bb5f-c91212149fd8
-- title:
--   Positive event contains an integrable geometric section
-- statement:
--   Every positive-probability event contains a geometric section that is integrable when the product-space function is integrable.
-- source:
--   Fubini selection for A19 geometric countermodel.

import Mathlib
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_a19_positive_event_integrable_geometric_section
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : unitInterval) (A : Set Ω) (hA : P A ≠ 0)
    (f : Ω × Nat → Real)
    (hf : Integrable f (P.prod (geometricMeasure p))) :
    ∃ ω ∈ A, Integrable (fun k : Nat => f (ω, k)) (geometricMeasure p) := by sorry
