-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_joint_measurable_max_HJB_capped_expected_nonpos
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_joint_measurable_max_HJB_capped_expected_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:48:06.537693+00:00
-- url     : https://prove2.me/theorems/9a09c1f5-45fc-411c-be13-6c456b1b2abc
-- title:
--   Original BV capped expected generator from joint-measurable actual stopped physical HJB
-- statement:
--   For the unchanged original Levy X, controlled dividend D and physical BV generator K, ordinary product measurability of the actual stopped-time region {p | p.1∈A p.2} and original joint K imply AEStronglyMeasurable stopped F. Combining exact original maximum HJB, positive capped region and integrable time envelope gives Gdrift L1 and nonpositive mean.
-- source:
--   Accepted original maximum-HJB capped generator expectation 9e6b876a, pinned Mathlib Measurable.ite and aestronglyMeasurable.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_max_HJB_exact_capped_expected_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_max_HJB_exact_physical_generator_sign
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_capped_HJB_time_envelope_expected_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_capped_HJB_implies_K_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_time_enveloped_generator_L1_and_Fubini
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_stopped_generator_L1_nonpos_mean
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_joint_measurable_max_HJB_capped_expected_nonpos {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
  (T : ℝ≥0) (μT : Measure ℝ≥0) [SFinite μT]
  (hTime : μT = (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))
  (A : Ω → Set ℝ≥0) (hAm : ∀ ω, MeasurableSet (A ω))
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
  (hASet : MeasurableSet {p : ℝ≥0 × Ω | p.1 ∈ A p.2})
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
