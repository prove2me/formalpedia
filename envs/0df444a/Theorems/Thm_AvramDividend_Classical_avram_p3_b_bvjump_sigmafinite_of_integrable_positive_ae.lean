-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_sigmafinite_of_integrable_positive_ae
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_sigmafinite_of_integrable_positive_ae
-- status  : Open
-- author  : @WillR
-- created : 2026-11-04T00:14:16.853107+00:00
-- url     : https://prove2.me/theorems/1a393882-1c79-4f61-b284-409b2d8a57d5
-- title:
--   Positive a.e. integrable real weight implies sigma-finiteness of any measure
-- statement:
--   Any measurable-space measure admitting an almost-everywhere strictly positive integrable real weight is sigma-finite: the countable superlevel sets {f≥1/(n+1)} each have finite measure by Integrable.measure_ge_lt_top, and together with the null set {f≤0} cover the space. In the Avram BV original-source application, f(z)=-z on the negative punctured mark band is positive a.e. and integrable by bounded variation, so the theorem furnishes the exact missing sigma-finiteness bridge for Bochner jump-mark integration.
-- source:
--   Mathlib Integrable.measure_ge_lt_top, Measure.sigmaFinite_of_countable and exists_nat_one_div_lt

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.avram_p3_b_bvjump_sigmafinite_of_integrable_positive_ae {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) : SigmaFinite μ := by sorry
