-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_finite_horizon_negative_C2_generator_signed_drift_L1_tendsto_zero
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_negative_C2_generator_signed_drift_L1_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:02:09.024813+00:00
-- url     : https://prove2.me/theorems/8e843521-1838-41cc-8690-f33d3d023167
-- title:
--   Original Lévy X.generator nonlinear jump drift band truncations vanish in finite-horizon physical L1
-- statement:
--   For the original spectrally negative Lévy process X, adapted dividend control D and compactly localised interior C² w, the signed generatorIntegrand of w at the actual prepayment reserve, ruin-stopped and integrated against original X.nu over any decreasing measurable negative bands with empty intersection, converges to zero in the original finite-horizon time×P L1 sense. The generator-form identity is from the actual-source Proved theorem 5e3be45e, and the physical L1 tail from a82fa765; this does not assume independent Poisson source or martingale compensation.
-- source:
--   Canonical Proved 5e3be45e original X generator drift equality, a82fa765 original physical P L1 and L2 source tails, pinned Mathlib ENorm integral and order squeeze.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_physical_L1_L2_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_negative_C2_generator_signed_drift_L1_tendsto_zero
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
      ‖∫ z in B n, JG (p,z) ∂X.ν‖ₑ ∂
      (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
      atTop (𝓝 0) := by sorry
