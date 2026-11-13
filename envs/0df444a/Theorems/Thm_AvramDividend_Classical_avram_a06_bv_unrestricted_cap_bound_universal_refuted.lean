-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_bv_unrestricted_cap_bound_universal_refuted
-- name    : AvramDividend.Classical.avram_a06_bv_unrestricted_cap_bound_universal_refuted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:47:31.949656+00:00
-- url     : https://prove2.me/theorems/405b5eb2-bd40-4e91-b394-2d70950bd212
-- title:
--   The uncorrected broad bounded-variation cash verification bound is false at zero cap
-- statement:
--   Formal polymorphic negation of the historical unrestricted-cap bounded-variation expected dividend budget. The broad theorem omits hypotheses found in the already refuted stochastic core and therefore logically implies that false core. This confirms the stronger statement is unsound as written.
-- source:
--   Proved polymorphic refutation f28d4aa6, plus exact A06 broad bound 65617e0a and original stochastic core 3296bf8a; preservation of source and conclusion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
universe u

theorem AvramDividend.Classical.avram_a06_bv_unrestricted_cap_bound_universal_refuted :
    ¬ (∀     {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (T : ℝ) (hT : 0 ≤ T) ,
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) ) := by sorry
