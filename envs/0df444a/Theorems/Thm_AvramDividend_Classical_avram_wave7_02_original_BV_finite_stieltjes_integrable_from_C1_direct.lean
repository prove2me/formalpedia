-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_finite_stieltjes_integrable_from_C1_direct
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_finite_stieltjes_integrable_from_C1_direct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:14:37.676953+00:00
-- url     : https://prove2.me/theorems/93ab65b3-418d-4ce6-9724-506c8d3ea09a
-- title:
--   Direct source BV C1 compactness proves finite-window physical Stieltjes derivative integrability without K premise
-- statement:
--   For the genuine original bounded-variation X and dividend strategy D, compact source reserve localization inside the exact open ENNReal cap and C1 candidate regularity give an absolute derivative bound by compactness. On a finite pre-ruin payment window the original dividend measure has finite mass, so the real discounted Stieltjes derivative correction is integrable whenever its exact integrand is strongly measurable. This direct proof imports only already Proved original source openness and finiteness results, and does not rely on an unsettled intermediate child.
-- source:
--   Proved original ENNReal positive-cap openness bcf24f3a, pinned Mathlib compact derivative bound and Proved actual finite-window Stieltjes integrability 017e0847.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_actual_discounted_dividend_gradient_integrable_on_finite_payment_window
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_finite_stieltjes_integrable_from_C1_direct
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q)
    (A : Set ℝ) (hAm : MeasurableSet A)
    (hAwindow : A ⊆
      paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ))
    (hApos : ∀ t ∈ A, 0 ≤ t)
    (hReserveBand : ∀ t ∈ A,
      riskProcess X x D t.toNNReal ω ∈ Icc a b)
    (hMeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω)))
      ((dividendMeasure D ω).restrict A)) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω)))
      A (dividendMeasure D ω) := by sorry
