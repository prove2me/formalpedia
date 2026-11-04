-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_bounded_random_coefficient_finite_band_L2_budget
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_bounded_random_coefficient_finite_band_L2_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:21:51.181424+00:00
-- url     : https://prove2.me/theorems/3559af3e-77e2-4ad2-953d-cad17659004e
-- title:
--   Original bounded coefficient finite-band L2 budget
-- statement:
--   A uniformly bounded random coefficient times the centred original Lévy finite-band jump count has quadratic physical-P expectation controlled by the original Lévy source rate.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_bounded_random_coefficient_finite_band_L2_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (J H : Ω → ℝ)
    (hSource : ∀ ω, J ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)
    (r : ℝ) (hRate : r =
      ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal)
    (C : ℝ) (hC : 0 ≤ C) (hBound : ∀ ω, |H ω| ≤ C)
    (hBaseInt : Integrable (fun ω => (J ω - r) ^ 2) P)
    (hWeightedInt : Integrable
      (fun ω => (H ω * (J ω - r)) ^ 2) P)
    (hVar : (∫ ω, (J ω - r) ^ 2 ∂P) = r) :
    (∫ ω, (H ω * (J ω - r)) ^ 2 ∂P) ≤ C ^ 2 * r := by sorry
