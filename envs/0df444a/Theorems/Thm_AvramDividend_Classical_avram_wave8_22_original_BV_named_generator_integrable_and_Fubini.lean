-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_named_generator_integrable_and_Fubini
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_named_generator_integrable_and_Fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:01:17.974641+00:00
-- url     : https://prove2.me/theorems/4e9345c9-6612-4cd9-a45d-4149e515cb76
-- title:
--   Original bounded-variation source physical named generator is integrable with exact Fubini expectation
-- statement:
--   For the original Levy X and true stopped physical-generator integral, the source product L1 condition transfers to the named drift random variable, giving source fibre L1, its integrability on original P and the exact physical generator Fubini expectation. The hGDef hypothesis is the literal actual source integral, not a centring or optional stopping assumption.
-- source:
--   Accepted original source physical time Fubini theorem 16b94421-9ad3-4b65-a6c9-42632a3d2e3f and Mathlib Integrable.congr / integral_congr_ae.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_stopped_generator_product_L1_all_fibre_and_mean
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_named_generator_integrable_and_Fubini {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
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
  (hGDef : ∀ᵐ ω ∂P, Gdrift ω = ∫ t in A ω, K t ω ∂μT) :
  (∀ᵐ ω ∂P, IntegrableOn (fun t => K t ω) (A ω) μT) ∧
  Integrable Gdrift P ∧
  (∫ ω, Gdrift ω ∂P) =
    (∫ p, F p ∂(μT.prod P)) := by sorry
