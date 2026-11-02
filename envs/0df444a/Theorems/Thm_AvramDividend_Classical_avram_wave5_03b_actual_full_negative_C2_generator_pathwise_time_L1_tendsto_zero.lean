-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_full_negative_C2_generator_pathwise_time_L1_tendsto_zero
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_full_negative_C2_generator_pathwise_time_L1_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:18:08.138529+00:00
-- url     : https://prove2.me/theorems/6004d52f-32fa-4ce5-bca4-b04349e9d1a4
-- title:
--   Actual controlled Lévy nonlinear generator finite-band correction converges pathwise in finite-time L1
-- statement:
--   For the literal original spectrally negative Lévy X, adapted dividend D, inclusive ruin stop and interior C² reward w, the signed source-generator drift lost by discarding any decreasing negative-mark bands has vanishing time-integrated ENorm for EVERY original sample path ω, against EVERY finite deterministic time measure μ. This is stronger than average time×P convergence and directly gives the nonlinear compensator drift time-integral limit, using only X.ν and no independent Poisson process. It deliberately does not assert a compensated P-martingale.
-- source:
--   Canonical Proved actual-source uniform stopped nonlinear generator drift band-to-full error, UUID 166d9c11-2e30-405f-bcc7-47049f0850d1; pinned Mathlib lintegral_mono, lintegral_const, ENNReal.Tendsto.const_mul and squeeze_zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_full_negative_C2_generator_band_to_full_uniform

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_full_negative_C2_generator_pathwise_time_L1_tendsto_zero
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
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅)
    (μ : Measure ℝ≥0) (hμ : μ Set.univ ≠ ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∀ ω : Ω, Tendsto
      (fun n : ℕ => ∫⁻ q : ℝ≥0,
        ‖(∫ z in Iio (0 : ℝ), JG ((q,ω),z) ∂X.ν) -
          (∫ z in Iio (0 : ℝ) \ B n, JG ((q,ω),z) ∂X.ν)‖ₑ ∂μ)
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
