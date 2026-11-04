-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_all_countable_finite_band_counts_ae_finite
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_all_countable_finite_band_counts_ae_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:29:55.590091+00:00
-- url     : https://prove2.me/theorems/e20b561e-82e1-4182-a2c8-7752387f1fe3
-- title:
--   Almost every original Levy path has finite intrinsic marked counts at all countably many cutoffs
-- statement:
--   For countably many original marked jump-count bands with finite original Levy intensities and verified first moment rates, one common full-measure physical event has finite marked count at every band cutoff.
-- source:
--   Original physical Levy count-moment theorem previously accepted, and pinned Mathlib ae_all_iff countable intersection.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_intensity_count_integrable_and_ae_finite

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_all_countable_finite_band_counts_ae_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : ℕ → Set ℝ)
    (J : ℕ → Ω → ℝ≥0∞)
    (hJsource : ∀ n ω, J n ω =
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B n))
    (hMeas : ∀ n, Measurable (J n))
    (hRate : ∀ n, (∫⁻ ω, J n ω ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B n)))
    (hFinite : ∀ n, X.ν (B n) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ n, J n ω < ⊤ := by sorry
