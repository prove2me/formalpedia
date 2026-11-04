-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_random_coeff_time_mark_grid_lintegral
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_random_coeff_time_mark_grid_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:47:07.334845+00:00
-- url     : https://prove2.me/theorems/b0252aab-cf24-45aa-beb6-476702a04dd9
-- title:
--   True original Lévy intrinsic integral of a random finite time-mark simple grid
-- statement:
--   For arbitrary finitely many physical time-mark rectangles and original-path random nonnegative coefficients, the literal original Levy intrinsic marked-jump simple integral is the weighted original-path count sum.
-- source:
--   Original intrinsic Levy marked jump measure and pinned Mathlib finite-sum lintegral, indicator_const identities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_random_coeff_time_mark_grid_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (B : ι → Set ℝ)
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞) (ω : Ω) :
    (∫⁻ p : ℝ≥0 × ℝ,
      ∑ i ∈ S, (Ioc (s i) (t i) ×ˢ B i).indicator
        (fun _ => H i ω) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑ i ∈ S, H i ω *
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) := by sorry
