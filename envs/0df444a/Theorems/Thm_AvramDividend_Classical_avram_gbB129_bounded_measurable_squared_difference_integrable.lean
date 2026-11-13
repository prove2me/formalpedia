-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB129_bounded_measurable_squared_difference_integrable
-- name    : AvramDividend.Classical.avram_gbB129_bounded_measurable_squared_difference_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T07:47:43.550547+00:00
-- url     : https://prove2.me/theorems/df2cf90e-937e-4772-bc80-566a64237d2a
-- title:
--   Finite-measure integrability of the square of a difference of uniformly bounded measurable functions
-- statement:
--   On a finite measure space, two measurable real functions whose absolute values are each bounded by B have an integrable squared difference. By the triangle inequality the absolute difference is bounded by 2B, hence the square is bounded by 4B squared, and measurable bounded functions are integrable. Used in B127's three inner probability integrability obligations.
-- source:
--   Mathlib MeasureTheory.Integrable.of_bound on finite measure spaces.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_gbB129_bounded_measurable_squared_difference_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ ω, |f ω| ≤ B) (hgb : ∀ ω, |g ω| ≤ B) :
    Integrable (fun ω => (f ω - g ω) ^ 2) P := by sorry
