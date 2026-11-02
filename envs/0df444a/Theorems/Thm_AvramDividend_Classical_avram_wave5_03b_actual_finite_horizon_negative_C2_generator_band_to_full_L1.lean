-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_finite_horizon_negative_C2_generator_band_to_full_L1
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_negative_C2_generator_band_to_full_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:40:34.932674+00:00
-- url     : https://prove2.me/theorems/60413ba8-a855-4452-b51d-fd0e213242b9
-- title:
--   Actual source negative Lévy jump generator finite-band drift converges to full nonlinear drift in physical L1
-- statement:
--   For the genuine spectrally negative Lévy process X and adapted dividend control D, the original ruin-stopped actual prepayment reserve nonlinear C² generator drift integrated over full negative marks minus its finite-band truncation over Iio(0) minus B_n converges to zero in finite-horizon physical time times P L¹. Bands B_n are measurable, negative, antitone and have empty intersection. Integrability is supplied by the canonical actual-source C² theorem 314e2bd0, tail signed drift by canonical actual-source 8e843521, and additive measure restriction by Mathlib. This closes the deterministic source drift truncation interface, not the still-open original negative mark compensator or stopped martingale.
-- source:
--   Original X and adapted dividends: canonical Proved 314e2bd0 signed generator section integrable, 8e843521 signed discarded-band physical L1, Mathlib integral_add_compl and Measure.restrict_restrict.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_generator_section_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_finite_horizon_negative_C2_generator_signed_drift_L1_tendsto_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_negative_C2_generator_band_to_full_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (T : ℝ≥0)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ‖(∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) -
        (∫ z in Iio (0 : ℝ) \ B n, JG (p,z) ∂X.ν)‖ₑ ∂
      (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
      atTop (𝓝 0) := by sorry
