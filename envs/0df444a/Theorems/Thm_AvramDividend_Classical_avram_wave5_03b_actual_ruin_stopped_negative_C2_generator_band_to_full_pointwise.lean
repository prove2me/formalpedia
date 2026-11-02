-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_negative_C2_generator_band_to_full_pointwise
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_negative_C2_generator_band_to_full_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:47:37.36275+00:00
-- url     : https://prove2.me/theorems/d1bf930e-2505-4b80-9e54-84205fa32bd2
-- title:
--   Genuine actual original reserve finite-band stopped nonlinear generator drift converges at every time and sample
-- statement:
--   For every time t and every sample ω of the original spectrally negative Lévy X with adapted dividend strategy D, the ruin-stopped prepayment reserve localised C² generator ν integral over retained negative marks Iio0\B_n converges pointwise to the full original negative-mark generator ν integral, for any decreasing measurable negative discarded bands with empty intersection. This is pathwise deterministic generator truncation, independent of probability exceptional sets, using the actual source X.nu and canonical integrable generator section 314e2bd0. It does not assert stochastic compensated martingale convergence.
-- source:
--   Canonical Proved 314e2bd0 genuine original-source stopped generator ν-section integrability; pinned Mathlib MeasureTheory.tendsto_setIntegral_of_monotone and exact union of retained negative mark sets.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_generator_section_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_negative_C2_generator_band_to_full_pointwise
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
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∀ p : ℝ≥0 × Ω,
      Tendsto (fun n : ℕ =>
        ∫ z in Iio (0 : ℝ) \ B n, JG (p,z) ∂X.ν)
        atTop (𝓝 (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν)) := by sorry
