-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18c_original_smallband_uniform_cutoff_difference_rate
-- name    : AvramDividend.Classical.avram_ja18c_original_smallband_uniform_cutoff_difference_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T22:47:00.555441+00:00
-- url     : https://prove2.me/theorems/99422ce0-558e-477a-a723-0127385d305d
-- title:
--   Uniform-on-bounded-clock original small-band cutoff difference rate 1 over n
-- statement:
--   For every original finite-count path and bounded horizon T, the difference between any two compensated physical small-band cutoffs n ≤ m, uniformly at times t ≤ T, is bounded by (physical total negative count at T plus source compensator T νnegative) / (n+1). Prove using Proved intrinsic original Gaussian cutoff difference bound 1b696ff5, exact compensated source residual identity 2c95a423, and monotonicity of the original marked count and deterministic compensator in t. Supplies explicit pathwise Cauchy modulus for child 678e826a of 23979329.
-- source:
--   Exact physical finite-activity bounded-clock quantitative cutoff modulus, not a hypothesis about a Brownian driver or large-mark first moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_anoise19_original_gaussian_residual_cutoff_count_bound
import Theorems.Thm_AvramDividend_Classical_avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18c_original_smallband_uniform_cutoff_difference_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (ω : Ω)
    (hNfin :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) < ⊤) :
    ∀ n m : ℕ, n ≤ m → ∀ t : ℝ≥0, t ≤ T →
      |avram_p4_h_gaussian_intrinsic_small_band_compensated X m t ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω| ≤
      (1 / ((n : ℝ) + 1)) *
        ((((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal +
        ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) := by sorry
