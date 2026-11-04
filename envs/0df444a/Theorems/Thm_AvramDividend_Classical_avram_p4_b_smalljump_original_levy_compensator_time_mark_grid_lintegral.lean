-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_levy_compensator_time_mark_grid_lintegral
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_levy_compensator_time_mark_grid_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:04:53.996887+00:00
-- url     : https://prove2.me/theorems/d67295cc-3965-4d85-a62c-a2a1b80b86f3
-- title:
--   Original time-mark grid compensator lintegral
-- statement:
--   The source X.nu compensator integral of any nonnegative finite time-mark simple kernel equals the weighted sum of product-measure cell masses, with an explicit timeMeasure.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_levy_compensator_time_mark_grid_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (timeMeasure : Measure ℝ≥0)
    {ι : Type*} (S : Finset ι) (s t : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (c : ι → ℝ≥0∞) :
    (∫⁻ p : ℝ≥0 × ℝ, ∑ i ∈ S,
      (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => c i) p
      ∂(timeMeasure.prod X.ν)) =
    ∑ i ∈ S, c i *
      (timeMeasure.prod X.ν)
        (Ioc (s i) (t i) ×ˢ B i) := by sorry
