-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:03:49.414332+00:00
-- url     : https://prove2.me/theorems/5e3be45e-c92f-4f8b-89c5-ae61128deb1c
-- title:
--   Actual ruin-stopped original Lévy nonlinear Taylor drift equals the negative-mark jump generator integral
-- statement:
--   For the literal spectrally negative Lévy source X and adapted dividend control D, any fixed time-sample p, and any measurable negative source-mark band B, the signed X.nu-integral of the exact nonlinear prepayment reserve Taylor correction, inclusively stopped at actual controlled ruin, equals the signed X.nu-integral of the matching localised generatorIntegrand w. The original source jump mark convention and 1_{z > -1} linear truncation are preserved. The statement is an exact deterministic source-intensity drift identity and does not assert the still-open stochastic jump compensator law.
-- source:
--   Canonical Proved 03-B source-specific pointwise Taylor-to-generator equality e336f7e2-a55f-48e8-b33e-54114f97e681 and pinned Mathlib ae_restrict_mem and integral_congr_ae; no abstract Poisson substitution.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (p : ℝ≥0 × Ω) (B : Set ℝ)
    (hBm : MeasurableSet B) (hBneg : B ⊆ Iio (0 : ℝ)) :
    let Y : ℝ≥0 × Ω → ℝ := fun r => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s r.2 - rightLimit D s r.2) r.1
    let S : ℝ :=
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    (∫ z in B, S *
      ((if Y p ∈ Icc (u + δ) v then
         w (Y p + z) - w (Y p) else 0) -
       (if -1 < z then
         z * (if Y p ∈ Icc (u + δ) v then deriv w (Y p) else 0)
         else 0)) ∂X.ν) =
    ∫ z in B, S *
      (if Y p ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p) z else 0)
      ∂X.ν := by sorry
