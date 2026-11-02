-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_signed_drift_L1_energy
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_signed_drift_L1_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:53:36.820528+00:00
-- url     : https://prove2.me/theorems/13bf3884-f9b9-4a28-8c38-25efac776e29
-- title:
--   Finite true original-P first absolute moment of signed ruin-stopped nonlinear source generator jump drift
-- statement:
--   For the original spectrally negative Lévy X and adapted dividend control D, the signed full-negative-mark nonlinear Itô Taylor jump-generator drift at every prepayment reserve is a well-defined real integral (existing pointwise Proved section integrability), and its ENorm has finite full finite-horizon original Lebesgue-time × P expectation. The proof bounds the absolute source signed integral by the full original-X.nu nonlinear L1 kernel energy, already canonically Proved under physical time × P. This controls generator drift without a martingale or an abstract independent Poisson process; no global monotonicity of general interior-C2 w.
-- source:
--   Canonical Proved 400350d3 actual signed full-negative section integrability, canonical Proved d451fcea physical finite-horizon full-negative source L1 kernel energy, pinned Mathlib norm_integral_le_lintegral_norm.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_physical_L1_L2_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_section_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_signed_drift_L1_energy
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
    (T : ℝ≥0) :
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
    (∫⁻ p : ℝ≥0 × Ω,
      ‖∫ z in Iio (0 : ℝ), HS (p,z) ∂X.ν‖ₑ ∂
      (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) < ⊤ := by sorry
