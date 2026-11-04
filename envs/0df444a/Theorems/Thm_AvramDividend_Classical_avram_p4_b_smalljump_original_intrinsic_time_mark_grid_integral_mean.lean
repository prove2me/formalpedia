-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_time_mark_grid_integral_mean
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_time_mark_grid_integral_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:52:00.737352+00:00
-- url     : https://prove2.me/theorems/cc8dc1fc-1c27-455e-86ba-4c17c4110b2c
-- title:
--   Original intrinsic finite time-mark jump-grid integral has source P2 mean
-- statement:
--   Given original-source physical P mean rates of the intrinsic jumps in each arbitrary measurable time-mark rectangle, the original intrinsic nonnegative finite-grid jump integral has the corresponding sum of Levy intensity weighted time lengths.
-- source:
--   Source-exact original SpectrallyNegativeLevy X.X, X.nu and Mathlib lintegral_indicator_const, lintegral_finset_sum and lintegral_const_mul at pinned Mathlib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_time_mark_grid_integral_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι) (s t : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (c : ι → ℝ≥0∞) (J : ι → Ω → ℝ≥0∞)
    (hJsource : ∀ i ω, J i ω =
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i))
    (hMeas : ∀ i ∈ S, Measurable (J i))
    (hRate : ∀ i ∈ S, (∫⁻ ω, J i ω ∂P) =
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) :
    (∫⁻ ω, (∫⁻ p : ℝ≥0 × ℝ,
      ∑ i ∈ S, (Ioc (s i) (t i) ×ˢ B i).indicator
        (fun _ => c i) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) =
    ∑ i ∈ S, c i * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by sorry
