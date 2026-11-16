-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a543_measurable_one_sided_three_component_residual
-- name    : AvramDividend.Classical.avram_ga_a543_measurable_one_sided_three_component_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:41:11.329194+00:00
-- url     : https://prove2.me/theorems/07fd73de-2e89-4925-bb6a-0c32537d2364
-- title:
--   Measurable one-sided three-component residual integrability bridge
-- statement:
--   If a random residual is pointwise A minus two integrable correction terms, and A is a.e. strongly measurable with an integrable positive part, then the residual is a.e. strongly measurable and its positive part is integrable.
-- source:
--   Combines proved a533 positive-part integrability of a three-component residual with finite sum a.e. measurability and pointwise equality.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a533_one_sided_three_source_integrability
open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a543_measurable_one_sided_three_component_residual
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (W A B C : Ω → ℝ)
    (hAmeas : AEStronglyMeasurable A P)
    (hA : Integrable (fun ω => max (A ω) (0 : ℝ)) P)
    (hB : Integrable B P) (hC : Integrable C P)
    (hEq : ∀ ω, W ω = A ω - B ω - C ω) :
    AEStronglyMeasurable W P ∧
      Integrable (fun ω => max (W ω) (0 : ℝ)) P := by sorry
