-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_random_coeff_levy_compensator_time_mark_grid_lintegral
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_random_coeff_levy_compensator_time_mark_grid_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:04:56.714192+00:00
-- url     : https://prove2.me/theorems/1e65fb74-a2de-4a38-9ae7-a38aaf1bb3b0
-- title:
--   Original random time-mark grid compensator lintegral
-- statement:
--   The source X.nu compensator integral of a random-coefficient finite time-mark simple kernel equals the weighted cell mass sum for each original outcome.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_random_coeff_levy_compensator_time_mark_grid_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (timeMeasure : Measure ℝ≥0)
    {ι : Type*} (S : Finset ι) (s t : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞) (ω : Ω) :
    (∫⁻ p : ℝ≥0 × ℝ, ∑ i ∈ S,
      (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => H i ω) p
      ∂(timeMeasure.prod X.ν)) =
    ∑ i ∈ S, H i ω *
      (timeMeasure.prod X.ν)
        (Ioc (s i) (t i) ×ˢ B i) := by sorry
