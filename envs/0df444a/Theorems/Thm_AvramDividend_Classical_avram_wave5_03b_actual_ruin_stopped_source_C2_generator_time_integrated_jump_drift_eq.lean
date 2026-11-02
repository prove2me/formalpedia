-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_C2_generator_time_integrated_jump_drift_eq
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_source_C2_generator_time_integrated_jump_drift_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:47:01.271859+00:00
-- url     : https://prove2.me/theorems/06ab55dc-e89a-4224-8fca-82094a2f8908
-- title:
--   Original Lévy prepayment stopped nonlinear Taylor drift equals generator jump drift after actual time integration
-- statement:
--   For the genuine controlled spectrally negative Lévy X and adapted D, on any negative measurable source mark band and any interval (s,t], the original inclusive-ruin-stopped nonlinear C² Taylor compensator drift integrated against the genuine Lévy measure ν and an arbitrary time measure μ is exactly the integrated generator jump drift. This lifts the proved source pointwise identity to the time integrated expression Chat 03 needs, without assuming a compensator law or asserting a martingale.
-- source:
--   Imports only canonical Proved original source pointwise stopped Taylor drift = Lévy generator-integrand drift 5e3be45e-c92f-4f8b-89c5-ae61128deb1c. No Poisson surrogate, independence, or martingale construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_source_C2_generator_time_integrated_jump_drift_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (s t : ℝ≥0) (ω : Ω)
    (μ : Measure ℝ≥0)
    (B : Set ℝ) (hBm : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ)) :
    let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun a : ℝ≥0 => x + X.X a ω - rightLimit D a ω) r
    let S : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) ≤ ruinTime X x D ω then 1 else 0
    (∫ r in Ioc s t, (∫ z in B, S r *
      ((if Y r ∈ Icc (u + δ) v then
        w (Y r + z) - w (Y r) else 0) -
       (if -1 < z then
        z * (if Y r ∈ Icc (u + δ) v then deriv w (Y r) else 0)
        else 0)) ∂X.ν) ∂μ) =
    (∫ r in Ioc s t, (∫ z in B, S r *
      (if Y r ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y r) z else 0)
      ∂X.ν) ∂μ) := by sorry
