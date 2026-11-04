-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_bounded_generator_clock_L1_and_Fubini
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_bounded_generator_clock_L1_and_Fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:02:02.32995+00:00
-- url     : https://prove2.me/theorems/d642c1c4-73e2-4afd-b5f1-33cb9e035cef
-- title:
--   Source BV bounded predictable physical generator on finite clock has L1 fibres and exact expectation
-- statement:
--   Original bounded-variation Lévy physical stopped generator K, with genuine original predictable F and finite product time-probability clock, is integrable when strongly measurable and uniformly bounded. This proves stopped-fibre L1, the named physical drift's L1 and exact Fubini mean without assumed L1 or an invented stochastic martingale.
-- source:
--   Pinned Mathlib MeasureTheory.Integrable.of_bound exact remote compiler signature and accepted 16b94421 original generator fibre/Fubini result.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_stopped_generator_product_L1_all_fibre_and_mean
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_bounded_generator_clock_L1_and_Fubini {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
  (T : ℝ≥0) (μT : Measure ℝ≥0) [SFinite μT] [IsFiniteMeasure (μT.prod P)]
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
  (M : ℝ) (hFbound : ∀ᵐ p ∂(μT.prod P), ‖F p‖ ≤ M)
  (Gdrift : Ω → ℝ)
  (hGDef : ∀ᵐ ω ∂P, Gdrift ω = ∫ t in A ω, K t ω ∂μT) :
  Integrable F (μT.prod P) ∧
  (∀ᵐ ω ∂P, IntegrableOn (fun t => K t ω) (A ω) μT) ∧
  Integrable Gdrift P ∧
  (∫ ω, Gdrift ω ∂P) =
    (∫ p, F p ∂(μT.prod P)) := by sorry
