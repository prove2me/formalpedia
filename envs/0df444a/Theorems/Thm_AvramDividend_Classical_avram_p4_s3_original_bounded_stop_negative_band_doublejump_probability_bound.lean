-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_doublejump_probability_bound
-- name    : AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_doublejump_probability_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:12:11.07435+00:00
-- url     : https://prove2.me/theorems/c9ffdee3-c16f-4ec1-a259-473f8623e9fd
-- title:
--   Exact original negative-band multi-jump probability bound at any bounded random ruin clock
-- statement:
--   For the original spectrally negative Lévy process and any sample-dependent horizon τ bounded pathwise by T, the probability of two or more negative-band jumps before τ is at most half the squared deterministic intensity (Tν(B))². This transfers the accepted original deterministic-band collision bound through pathwise finite jump-set inclusion to the genuine stopped clock, without equality-in-law or a stopping-time axiom.
-- source:
--   Original negative-band marked times finite theorem avram_wave7_06_original_negative_band_marked_times_finite and accepted source double-jump probability bound 6253d62d-750d-4e39-81fe-5c99fac375ea; monotonicity of finite ncard and probability outer measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_doublejump_probability_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    P.real {ω : Ω | 2 ≤ K ω} ≤ r ^ 2 / 2 := by sorry
