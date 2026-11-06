-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_factorial_highcount_tail
-- name    : AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_factorial_highcount_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:28:35.074021+00:00
-- url     : https://prove2.me/theorems/318d7b38-4a62-461a-bd0d-dffc513e767c
-- title:
--   Original stopped negative-band high-jump-count tails obey the exact second-order factorial bound
-- statement:
--   For an original spectrally negative Levy sample path and any bounded random stopping clock τ≤T with measurable intrinsic separated negative-band count K, every threshold m≥2 has P(K≥m)≤(Tν(Band)).toReal²/[m(m−1)]. This is a quadratic-in-time tail uniform in the original physical stopping clock and sharper for high counts than a square-energy Markov estimate.
-- source:
--   Apply newly accepted original stopped factorial pair moment b3b05dd5 and pointwise factorial Markov inequality m(m−1)·1_{K≥m}≤K(K−1), integrate the original source event indicator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_factorial_pair_moment
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_factorial_highcount_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard))
    (m : ℕ) (hm : 2 ≤ m) :
    let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    P.real {ω : Ω | m ≤ K ω} ≤
      r ^ 2 / ((m : ℝ) * ((m : ℝ) - 1)) := by sorry
