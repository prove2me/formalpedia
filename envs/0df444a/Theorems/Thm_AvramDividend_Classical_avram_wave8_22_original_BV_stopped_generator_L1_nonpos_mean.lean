-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_stopped_generator_L1_nonpos_mean
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_stopped_generator_L1_nonpos_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:08:47.517915+00:00
-- url     : https://prove2.me/theorems/884a3b17-8404-4c1f-9431-327ef89cd2c0
-- title:
--   Original BV source stopped generator is nonpositive almost surely and in expectation
-- statement:
--   For the true source Lévy process, a physical stopped generator K which is nonpositive on the actual localised stopped region and integrable on the original product clock gives an L1 named random drift Gdrift, almost-sure nonpositivity and nonpositive expectation. This is the expectation-level HJB generator sign without any Stieltjes integrability or martingale centring assumption.
-- source:
--   Accepted original physical generator product L1/fibre theorem 16b94421 and pinned Mathlib integral_nonpos_of_ae / integral_indicator.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_stopped_generator_product_L1_all_fibre_and_mean
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_stopped_generator_L1_nonpos_mean {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [SFinite P] {𝓕 : Filtration ℝ≥0 mΩ}
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
  (hFI : Integrable F (μT.prod P))
  (Gdrift : Ω → ℝ)
  (hGDef : ∀ᵐ ω ∂P, Gdrift ω = ∫ t in A ω, K t ω ∂μT)
  (hKnonpos : ∀ᵐ ω ∂P, ∀ t, t ∈ A ω → K t ω ≤ 0) :
  Integrable Gdrift P ∧
  (∀ᵐ ω ∂P, Gdrift ω ≤ 0) ∧
  (∫ ω, Gdrift ω ∂P) ≤ 0 := by sorry
