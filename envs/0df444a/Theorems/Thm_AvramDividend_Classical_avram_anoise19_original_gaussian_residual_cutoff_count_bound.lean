-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise19_original_gaussian_residual_cutoff_count_bound
-- name    : AvramDividend.Classical.avram_anoise19_original_gaussian_residual_cutoff_count_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T08:08:43.913405+00:00
-- url     : https://prove2.me/theorems/1b696ff5-c4df-41d0-a6a0-cece47125ed2
-- title:
--   Original Gaussian cutoff error dominated by full finite negative count and source rate
-- statement:
--   For one physical original Lévy sample path with finitely many negative jumps before the horizon, the difference of intrinsic Gaussian residuals at cutoffs n≤m has absolute value at most 1/(n+1) times the full negative-jump count plus T times the full negative Lévy intensity. The estimate is pathwise and uses only bounded small-negative marks, so no moment of the sizes of large jumps is assumed.
-- source:
--   Proved original residual cutoff identity 2c95a423, signed small-jump strip fe464249, source ν small-strip bound e9bcbe6c, and measure integral domination by strip cardinality. This bridges all-negative count L2 a6562a4d into residual L2 Cauchy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smalljump_cutoff_strip
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_anoise19_original_gaussian_residual_cutoff_count_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n m : ℕ) (hnm : n ≤ m) (T : ℝ≥0) (ω : Ω)
    (hNfin :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) < ⊤) :
    let N : ℝ≥0∞ :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))
    let A : ℝ := ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
    |avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω -
      avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω| ≤
      (1 / ((n : ℝ) + 1)) * (N.toReal + A) := by sorry
