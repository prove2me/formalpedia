-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_actual_stopped_jump_drift_indicator
-- name    : AvramDividend.Classical.avram_p4_c_generator_actual_stopped_jump_drift_indicator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:24:05.179713+00:00
-- url     : https://prove2.me/theorems/54b6ca71-bfa9-44e9-8d42-297d6540dd14
-- title:
--   Original ruin-stopped negative Levy generator compensator drift equals interior-event indicator
-- statement:
--   For the actual controlled prepayment left-limit surplus of the original spectrally negative Levy X, stopped at its exact ruinTime and restricted to an arbitrary compact reserve band, the integral of the masked nonlinear generator jump kernel against the original Levy measure X.nu equals the interior event indicator of the full source negative-mark generator integral. The identity has exact original mark signs and ruin-time endpoint, requires no invented stochastic compensator or out-of-band derivative. It converts the accepted source joint L1 estimate c254b492 into the generator-density form used in verification.
-- source:
--   Source definitions SpectrallyNegativeLevy.generatorIntegrand, ruinTime, rightLimit D; source accepted true-clock signed jump drift L1 c254b492-43ea-4b98-8f84-33a7c8bc65d6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_actual_stopped_jump_drift_indicator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (a b : ℝ) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let A : Set (ℝ≥0 × Ω) :=
      {p | (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧ Y p ∈ Icc a b}
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc a b then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∀ p : ℝ≥0 × Ω,
      (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) =
      A.indicator (fun p => ∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w (Y p) z ∂X.ν) p := by sorry
