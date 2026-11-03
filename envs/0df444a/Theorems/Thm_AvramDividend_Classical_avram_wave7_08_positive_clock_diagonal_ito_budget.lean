-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_positive_clock_diagonal_ito_budget
-- name    : AvramDividend.Classical.avram_wave7_08_positive_clock_diagonal_ito_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T14:00:47.826765+00:00
-- url     : https://prove2.me/theorems/9269710f-500f-4f11-8f69-f64363907887
-- title:
--   Canonical UBV strictly positive reserve source stopped Ito-Meyer cash budget at its natural finite clock
-- statement:
--   For arbitrary original-source spectrally negative Levy process including nonzero Levy jump measure, admissible D, x>0, q>0, w(0)>=0, positive n, and exact HJB and right dividend atom hypotheses, prove the expected full Stieltjes payout up to min(ruinTime,n) and horizon n is at most ENNReal.ofReal(w x). This is the remaining mixed-jump controlled Itô-Meyer estimate once payment-time support reduces arbitrary T to T=n.
-- source:
--   Exact no-T diagonal stochastic cutset of W7-08 d457be6b-c74a-4a7e-aea2-4bb6222642d5, reduced via Proved source payment-time support child 2cd84612 and proposed source cash monotonicity 7b9deff0. No model substitution or target weakening.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_positive_clock_diagonal_ito_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
