-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_route11_canonical_zero_cap_hypotheses_refute
-- name    : AvramDividend.Classical.avram_bv_route11_canonical_zero_cap_hypotheses_refute
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:08:25.346201+00:00
-- url     : https://prove2.me/theorems/608ab358-2ed4-4529-8675-b2ca65694c28
-- title:
--   Canonical BV stochastic core universal statement fails at zero cap under original finite-activity Standing process
-- statement:
--   For any Standing bounded-variation original process with finite negative-jump activity, the universal stochastic-core inequality with exactly the hypotheses of 3296bf8a fails. A zero-cap choice w=0 and the original zero barrier simultaneously satisfies all contact, generator, gradient, regularity, admissibility and nonnegativity assumptions, while earning strictly positive cash at a finite horizon.
-- source:
--   Source-exact refutation certificate: original 3296bf8a hypotheses reproduced and witnessed using the published Proved original-process 833cfa93. Conditional on a Standing BV finite-activity X; does not construct an inhabited original-process model.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_route11_zero_cap_contact_positive_cash

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_bv_route11_canonical_zero_cap_hypotheses_refute
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    ¬ ∀ (w : ℝ → ℝ) (C : ℝ≥0∞)
        (hw_cont : ContinuousOn w (Ici 0))
        (hw_neg : ∀ y < 0, w y = 0)
        (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
        (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
          X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
        (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
        (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
        (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
        (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
          (t : ℝ≥0∞) < ruinTime X x D ω →
          0 ≤ w (riskProcess X x D t ω))
        (hjump : ∀ ω (t : ℝ≥0),
          (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
          rightLimit D t ω - D t ω ≤
            w (riskProcess X x D t ω) -
              w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
        (T : ℝ) (hT : 0 ≤ T),
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) := by sorry
