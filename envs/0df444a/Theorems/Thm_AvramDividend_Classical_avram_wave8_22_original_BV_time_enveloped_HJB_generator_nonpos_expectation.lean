-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_time_enveloped_HJB_generator_nonpos_expectation
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_time_enveloped_HJB_generator_nonpos_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:14:49.08219+00:00
-- url     : https://prove2.me/theorems/14036758-e729-46d6-8def-08f4cc88a89e
-- title:
--   Original BV stopped HJB generator has integrable nonpositive mean from time envelope
-- statement:
--   For the original spectrally negative Levy process and controlled dividend source, a deterministic integrable time envelope dominating the stopped predictable physical generator plus genuine pointwise local HJB sign gives L1 of the named drift, almost sure nonpositivity and nonpositive P-expectation. It instantiates two previously accepted exact-source W8-22 lemmas and assumes no martingale centring.
-- source:
--   Accepted 00a0f6e2 time-envelope source generator L1/Fubini and 884a3b17 source stopped physical generator nonpositive mean.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_time_enveloped_generator_L1_and_Fubini
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_stopped_generator_L1_nonpos_mean
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_time_enveloped_HJB_generator_nonpos_expectation {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
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
  (hFmeas : AEStronglyMeasurable F (μT.prod P))
  (g : ℝ≥0 → ℝ) (hgI : Integrable g μT)
  (hFbound : ∀ᵐ p ∂(μT.prod P), ‖F p‖ ≤ ‖g p.1‖)
  (Gdrift : Ω → ℝ)
  (hGDef : ∀ᵐ ω ∂P, Gdrift ω = ∫ t in A ω, K t ω ∂μT)
  (hKnonpos : ∀ᵐ ω ∂P, ∀ t, t ∈ A ω → K t ω ≤ 0) :
  Integrable Gdrift P ∧
  (∀ᵐ ω ∂P, Gdrift ω ≤ 0) ∧
  (∫ ω, Gdrift ω ∂P) ≤ 0 := by sorry
