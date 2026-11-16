-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a533_one_sided_three_source_integrability
-- name    : AvramDividend.Classical.avram_ga_a533_one_sided_three_source_integrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:19:51.430325+00:00
-- url     : https://prove2.me/theorems/3e08ed66-8a12-4f3e-992e-829fed160070
-- title:
--   One-sided integrability for a signed three-component spatial residual
-- statement:
--   For real random components, the positive part of A-B-C is integrable when the positive part of A is integrable, B and C are integrable, and the result is almost-everywhere strongly measurable. No negative-tail moment of A is assumed.
-- source:
--   Pointwise domination max(A-B-C,0) <= max(A,0) + abs B + abs C, integrability and Integrable.mono_nonneg.

import Mathlib
open MeasureTheory Set Filter
noncomputable section

theorem AvramDividend.Classical.avram_ga_a533_one_sided_three_source_integrability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (A B C : Ω → ℝ)
    (hA : Integrable (fun ω => max (A ω) (0 : ℝ)) P)
    (hB : Integrable B P) (hC : Integrable C P)
    (hMeas : AEStronglyMeasurable
      (fun ω => max (A ω - B ω - C ω) (0 : ℝ)) P) :
    Integrable (fun ω => max (A ω - B ω - C ω) (0 : ℝ)) P := by sorry
