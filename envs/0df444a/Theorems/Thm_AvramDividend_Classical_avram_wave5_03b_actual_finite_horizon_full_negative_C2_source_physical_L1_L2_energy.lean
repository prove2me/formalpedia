-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_physical_L1_L2_energy
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_physical_L1_L2_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:30:01.050482+00:00
-- url     : https://prove2.me/theorems/d451fcea-6be7-4d53-bd2a-3bc04e4d3c3f
-- title:
--   Literal finite original time × P source-jump nonlinear absolute L¹ and quadratic L² energy for general C² test
-- statement:
--   For the actual original spectrally negative Lévy process and adapted dividend control, the stopped prepayment nonlinear compensated Taylor remainder has both finite absolute L1 source intensity and finite squared L2 source intensity directly under the genuine finite-horizon Lebesgue-time times original probability P measure. The predictable source energy theorem is transported through the original P finite-horizon predictable integration bridge and measurable source-mark Fubini kernel. Does not assume source jump Poisson independence or claim stochastic compensation.
-- source:
--   Canonical Proved 0e0663b1 source-coupled full negative C2 predictable L1/L2 energy and Proved 16857b34 physical time×P predictable bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_physical_L1_L2_energy
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
      ∫⁻ z in Iio (0 : ℝ), ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂
      (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) < ⊤ ∧
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in Iio (0 : ℝ), ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂
      (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) < ⊤ := by sorry
