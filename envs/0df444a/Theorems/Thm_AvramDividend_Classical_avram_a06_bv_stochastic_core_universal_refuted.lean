-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_bv_stochastic_core_universal_refuted
-- name    : AvramDividend.Classical.avram_a06_bv_stochastic_core_universal_refuted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T21:56:06.614437+00:00
-- url     : https://prove2.me/theorems/f28d4aa6-902f-49eb-b29b-5bd01e3f3966
-- title:
--   The universal A06 bounded-variation stochastic verification statement is false at zero dividend cap
-- statement:
--   A genuine finite-activity bounded-variation Standing spectrally negative Lévy source exists; for this source the original A06 hypotheses hold for cap C=0 and the zero value candidate, while admissible zero-barrier dividends violate the asserted finite-horizon cash bound. Hence the entire universally quantified A06 theorem is false as presently stated. This is the precise negation of the original target, rather than merely a conditional counterexample.
-- source:
--   Root A06 theorem 3296bf8a-aa23-478b-842f-104133415fdd. Uses verified concrete original-space source-existence 3281148e and verified original-hypothesis zero-cap violating witness 696ceb2d. The official direct-disproof endpoint cannot import theorem modules, so this proposed proved theorem exposes the negative proposition separately.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_bv_stochastic_core_universal_refuted :
    ¬ (∀ {Ω : Type*} [mΩ : MeasurableSpace Ω]
      {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
      (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
      (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
      (w : ℝ → ℝ) (C : ℝ≥0∞)
      (hw_cont : ContinuousOn w (Ici 0))
      (hw_neg : ∀ y < 0, w y = 0)
      (hw_smooth : ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
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
            w (riskProcess X x D t ω -
              (rightLimit D t ω - D t ω)))
      (T : ℝ) (hT : 0 ≤ T),
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x)) := by sorry
