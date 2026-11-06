-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_weighted_L1_rate
-- name    : AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_weighted_L1_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:23:19.70455+00:00
-- url     : https://prove2.me/theorems/806f38bd-bec0-4de6-a25a-53a754cff0b0
-- title:
--   Original bounded random-clock negative-band weighted count has first-order L1 Levy-intensity bound
-- statement:
--   For the original spectrally negative Levy path and a measurable bounded random-clock finite negative-band jump count, any measurable random coefficient bounded in absolute value by B yields an integrable weighted physical count with expected absolute value at most B times (Tν(Band)).toReal. This first-order source L1 bound is sharper than the L2-derived square-root estimate and supplies uniform physical clock localisation for P4-F3.
-- source:
--   Proved source original bounded-stop count first-moment lemma, pointwise |H*K|≤B*K and monotonicity of Bochner integrals. No independent Poisson law, equality-in-law, or new stochastic axiom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_count_L1_first_moment
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_weighted_L1_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard))
    (H : Ω → ℝ) (hHm : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hH : ∀ ω, |H ω| ≤ B) :
    let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => H ω * (K ω : ℝ)) P ∧
    (∫ ω, |H ω * (K ω : ℝ)| ∂P) ≤ B * r := by sorry
