-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_annulus18_original_shifted_centered_first_moment
-- name    : AvramDividend.Classical.avram_mix_annulus18_original_shifted_centered_first_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:17:41.559554+00:00
-- url     : https://prove2.me/theorems/d0efcb93-68a8-4a09-9ca1-7d903d29c6da
-- title:
--   Original shifted physical negative-annulus count has centred first moment
-- statement:
--   The original marked negative annulus count over every deterministic shifted time window has an integrable compensated first moment equal to zero. This directly consumes the Proved zero-origin first moment and source-exact same-path Lévy stationarity, supplying the first conditional moment input to the right-continuous finite-grid stopped martingale isometry.
-- source:
--   Root-connected original annulus conditional moment 5bb8fe6e; Proved source 6ddaed7b and same-path stationarity 34cdb144.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus16_original_zero_origin_centered_mean
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_annulus18_original_shifted_centered_first_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => (N ω).toReal - r) P ∧
      (∫ ω, (N ω).toReal - r ∂P) = 0 := by sorry
