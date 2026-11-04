-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_weighted_time_mark_grid_compensation_L1
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_P2_weighted_time_mark_grid_compensation_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:11:53.897965+00:00
-- url     : https://prove2.me/theorems/b798b5ef-d94e-4801-9a23-1870c4400b39
-- title:
--   Original P2 weighted finite time-mark grid compensation
-- statement:
--   Genuine cellwise original source P2 rate identities yield equality of physical-P expected original intrinsic mark jump integral and source Levy product compensator.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_random_coeff_time_mark_grid_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_random_coeff_levy_compensator_time_mark_grid_lintegral

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_P2_weighted_time_mark_grid_compensation_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (timeMeasure : Measure ℝ≥0)
    (N : Ω → Measure (ℝ≥0 × ℝ))
    (hN : ∀ ω, N ω =
      (Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    {ι : Type*} (S : Finset ι) (s t : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ S, Measurable (H i))
    (hCount : ∀ i ∈ S, Measurable
      (fun ω => N ω (Ioc (s i) (t i) ×ˢ B i)))
    (hRate : ∀ i ∈ S,
      (∫⁻ ω, H i ω * N ω (Ioc (s i) (t i) ×ˢ B i) ∂P) =
      (∫⁻ ω, H i ω *
        (timeMeasure.prod X.ν) (Ioc (s i) (t i) ×ˢ B i) ∂P)) :
    (∫⁻ ω, (∫⁻ p : ℝ≥0 × ℝ,
      ∑ i ∈ S, (Ioc (s i) (t i) ×ˢ B i).indicator
        (fun _ => H i ω) p ∂N ω) ∂P) =
    (∫⁻ ω, (∫⁻ p : ℝ≥0 × ℝ,
      ∑ i ∈ S, (Ioc (s i) (t i) ×ˢ B i).indicator
        (fun _ => H i ω) p ∂(timeMeasure.prod X.ν)) ∂P) := by sorry
