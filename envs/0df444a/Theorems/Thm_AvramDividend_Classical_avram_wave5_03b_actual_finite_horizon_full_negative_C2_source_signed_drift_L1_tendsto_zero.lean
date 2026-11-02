-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_signed_drift_L1_tendsto_zero
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_signed_drift_L1_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:00:19.108644+00:00
-- url     : https://prove2.me/theorems/1d40dbd0-4c83-45bb-94af-63ec6ebadd98
-- title:
--   Actual controlled stopped signed nonlinear source jump drift converges in physical L1 under negative-mark truncation
-- statement:
--   For the original spectrally negative Lévy process X, adapted dividend strategy D and general interior-C² w, the signed X.nu integral of the stopped predictable prepayment nonlinear Taylor source kernel over arbitrary measurable decreasing negative-mark bands with empty intersection converges to zero in expected ENorm under literal original finite-horizon Lebesgue time times P. This is the actual generator drift truncation step, not an independent-PRM statement or martingale compensation.
-- source:
--   Canonical Proved a82fa765 physical original-P L1/L2 source tails, pinned Mathlib enorm_integral_le_lintegral_enorm and tendsto_of_tendsto_of_tendsto_of_le_of_le.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_physical_L1_L2_tendsto_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_signed_drift_L1_tendsto_zero
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
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ‖∫ z in B n, HS (p,z) ∂X.ν‖ₑ ∂
      (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
      atTop (𝓝 0) := by sorry
