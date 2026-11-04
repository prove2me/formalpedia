-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_physical_stopped_generator_product_L1_to_random_expectation
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_physical_stopped_generator_product_L1_to_random_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:03:20.81544+00:00
-- url     : https://prove2.me/theorems/9c0aaa81-cfd2-4511-af72-9e2102062a8e
-- title:
--   Source BV physical stopped generator product L1 transports to original random time-integral L1 and exact expected value
-- statement:
--   For the actual original BV spectrally negative Levy process, its original left reserve and signed physical generator with actual negative Levy integral are encoded by the stopped function F on the source time-probability product clock. Under honest global product L1 and an actual almost-sure random time integral definition, prove Integrable Gdrift P and the Fubini equality E[Gdrift] = integral(F) against the true time-probability product. This is the precise source-specific generator random L1 bridge needed by W8-04 whenever it establishes predictable product integrability.
-- source:
--   Pinned Mathlib 0df444a MeasureTheory.Integrable.integral_prod_right and integral_prod_symm; physical generator source from W7-02 a0879a2f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_physical_stopped_generator_product_L1_to_random_expectation {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [SFinite P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
  (T : ℝ≥0) (μT : Measure ℝ≥0) [SFinite μT]
  (hTime : μT = (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))
  (E : Set (ℝ≥0 × Ω))
  (F : (ℝ≥0 × Ω) → ℝ)
  (hF : ∀ p, F p = if p ∈ E then
    Real.exp (-(q * (p.1 : ℝ))) *
      (X.drift * deriv w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) +
      (∫ z in Iio (0 : ℝ),
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.2 - rightLimit D s p.2) p.1 + z) -
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.2 - rightLimit D s p.2) p.1) ∂X.ν) -
      q * w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1)) else 0)
  (hFI : Integrable F (μT.prod P))
  (Gdrift : Ω → ℝ)
  (hGDef : ∀ᵐ ω ∂P, Gdrift ω = ∫ t, F (t, ω) ∂μT) :
  Integrable Gdrift P ∧
    (∫ ω, Gdrift ω ∂P) = (∫ p, F p ∂(μT.prod P)) := by sorry
