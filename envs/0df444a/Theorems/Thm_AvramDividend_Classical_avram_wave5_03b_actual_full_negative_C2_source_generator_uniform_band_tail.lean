-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_full_negative_C2_source_generator_uniform_band_tail
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_full_negative_C2_source_generator_uniform_band_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:50:52.106727+00:00
-- url     : https://prove2.me/theorems/8efe9f2d-2669-413c-a434-6d52da6f9be9
-- title:
--   Original Lévy stopped nonlinear generator negative-band errors vanish uniformly over every time and sample
-- statement:
--   For original spectrally negative Lévy X and an arbitrary adapted dividend control, the signed stopped nonlinear C² generator source ν integral on any measurable decreasing negative discarded bands admits a deterministic vanishing ENorm majorant err_n uniform simultaneously in all original time-path points p. Uses the genuine original ν quadratic Lévy integrability and the original controlled prepayment-reserve Taylor envelope with no extra global monotonicity of w. This is source drift truncation, not a stochastic compensated martingale limit.
-- source:
--   Proved 5eef1de0 uniform original source negative-mark C² Taylor envelope; Proved 5e3be45e genuine generator signed ν integral equality; Proved avram_wave4_p1_integrable_mark_energy_tail_iInf_zero quadratic original ν tail and pinned Mathlib ENNReal monotone convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_integrable_mark_energy_tail_iInf_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_full_negative_C2_source_generator_uniform_band_tail
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
    ∃ err : ℕ → ℝ≥0∞, Tendsto err atTop (𝓝 0) ∧
      ∀ n : ℕ, ∀ p : ℝ≥0 × Ω,
        ‖∫ z in B n, JG (p,z) ∂X.ν‖ₑ ≤ err n := by sorry
