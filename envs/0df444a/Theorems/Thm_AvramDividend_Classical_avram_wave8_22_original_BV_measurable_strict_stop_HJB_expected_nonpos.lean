-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_measurable_strict_stop_HJB_expected_nonpos
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_measurable_strict_stop_HJB_expected_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:57:04.250396+00:00
-- url     : https://prove2.me/theorems/709fbd4f-556a-499d-a084-cf944f1fa6f4
-- title:
--   Original BV expected stopped generator on a measurable strict stopping horizon
-- statement:
--   For original X and D, a measurable finite stopping clock τ gives measurable fibres A ω = Iio (τ ω) and an actual measurable product stopping region. The genuinely jointly measurable original physical stopped generator is therefore admissible to the accepted exact maximum-HJB expectation inequality.
-- source:
--   Accepted joint-measurability HJB expectation theorem 9a09c1f5 and pinned Mathlib measurableSet_lt; original strict stopping-time region.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_joint_measurable_max_HJB_capped_expected_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_max_HJB_exact_physical_generator_sign
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_capped_HJB_time_envelope_expected_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_time_enveloped_HJB_generator_nonpos_expectation
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_capped_HJB_implies_K_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_time_enveloped_generator_L1_and_Fubini
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_stopped_generator_L1_nonpos_mean
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Original stopped physical HJB generator has nonpositive expected drift when its true predictable product is dominated by an integrable time envelope. -/

theorem AvramDividend.Classical.avram_wave8_22_original_BV_measurable_strict_stop_HJB_expected_nonpos {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
  (T : ℝ≥0) (μT : Measure ℝ≥0) [SFinite μT]
  (hTime : μT = (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))
  (A : Ω → Set ℝ≥0) (τ : Ω → ℝ≥0)
  (hA : ∀ ω, A ω = Iio (τ ω)) (hτmeas : Measurable τ)
  (K : ℝ≥0 → Ω → ℝ)
  (hK : ∀ t ω, K t ω =
    Real.exp (-(q * (t : ℝ))) *
      (X.drift * deriv w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) +
      (∫ z in Iio (0 : ℝ),
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t + z) -
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t) ∂X.ν) -
      q * w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t)))
  (F : (ℝ≥0 × Ω) → ℝ)
  (hF : ∀ p, F p = if p.1 ∈ A p.2 then K p.1 p.2 else 0)
  (hKmeas : Measurable (fun p : ℝ≥0 × Ω => K p.1 p.2))
  (g : ℝ≥0 → ℝ) (hgI : Integrable g μT)
  (hFbound : ∀ᵐ p ∂(μT.prod P), ‖F p‖ ≤ ‖g p.1‖)
  (Gdrift : Ω → ℝ)
  (hGDef : ∀ᵐ ω ∂P, Gdrift ω = ∫ t in A ω, K t ω ∂μT)
  (C : ℝ≥0∞)
  (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.GeneratorIntegrable w y ∧
    max (X.generator w y - q * w y) (1 - deriv w y) = 0)
  (hRegion : ∀ᵐ ω ∂P, ∀ t, t ∈ A ω →
    0 < Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
    ENNReal.ofReal (Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C) :
  Integrable Gdrift P ∧
  (∀ᵐ ω ∂P, Gdrift ω ≤ 0) ∧
  (∫ ω, Gdrift ω ∂P) ≤ 0 := by sorry
