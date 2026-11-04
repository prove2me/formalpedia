-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_stopped_generator_product_L1_all_fibre_and_mean
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_stopped_generator_product_L1_all_fibre_and_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:12:36.826127+00:00
-- url     : https://prove2.me/theorems/16b94421-9ad3-4b65-a6c9-42632a3d2e3f
-- title:
--   Original BV stopped physical generator product L1 supplies both a.e. time-fibre L1 and random expected HJB generator L1
-- statement:
--   The actual source BV generator kernel, original physical time clock and true random stopped region A have an integrable product density F. Under explicit original product L1, prove both the P-almost-everywhere source time-fibre IntegrableOn needed for signed HJB and the P-Integrable random physical generator required by the finite horizon expectation budget, together with the exact Fubini expectation formula. Original Omega/P/filtration/X are preserved and no zero-mean assertion is assumed.
-- source:
--   Accepted source 0c8bc99e-f099-427e-a089-11071282761b plus pinned Mathlib Integrable.prod_left_ae and integrable_indicator_iff.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_stopped_physical_generator_restricted_time_fubini
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_stopped_generator_product_L1_all_fibre_and_mean {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
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
  (hFI : Integrable F (μT.prod P)) :
  (∀ᵐ ω ∂P, IntegrableOn (fun t => K t ω) (A ω) μT) ∧
  Integrable (fun ω => ∫ t in A ω, K t ω ∂μT) P ∧
  (∫ ω, ∫ t in A ω, K t ω ∂μT ∂P) =
    (∫ p, F p ∂(μT.prod P))  := by sorry
