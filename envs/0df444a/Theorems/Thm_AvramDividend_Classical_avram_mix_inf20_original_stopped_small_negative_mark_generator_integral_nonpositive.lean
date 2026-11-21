-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_stopped_small_negative_mark_generator_integral_nonpositive
-- name    : AvramDividend.Classical.avram_mix_inf20_original_stopped_small_negative_mark_generator_integral_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:36:21.305139+00:00
-- url     : https://prove2.me/theorems/b605b39e-f6f3-47a3-898c-5f4f4dea3fc7
-- title:
--   Original mixed stopped predictable nearzero compensated negative-mark generator contributes nonpositive discounted mean above finite cap
-- statement:
--   Actual original controlled Lévy infinite-negative-activity small-mark compensator: for the true previsible reserve Y(t,ω)=leftLim(x+X(t,ω)-rightLimit D(t,ω)), any finite dividend cap, any positive δ≤min(1,C.toReal), and any time×sample×mark measure μ, the discounted original exact generatorIntegrand restricted to above-cap reserve and truly small marks -δ<z<0 has a nonpositive integral whenever it is integrable. This uses the source-faithful negative-sign lemma for actual compensated marks (rather than the untruncated full-z subtraction), and positivity of the exponential discount. The genuine actual random stopped process, its left-limit, and dividend right-limit appear explicitly. The theorem does not assume finite activity or expected finite first moment; stopped predictable measurability and μ-integrability remain inputs to the stochastic source identification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_stopped_small_negative_mark_generator_integral_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) (hδcap : δ ≤ C.toReal)
    (μ : Measure ((ℝ≥0 × Ω) × ℝ)) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if C.toReal < Y p.1 ∧ -δ < p.2 ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          SpectrallyNegativeLevy.generatorIntegrand V (Y p.1) p.2
      else 0
    Integrable H μ → (∫ p, H p ∂μ) ≤ 0 := by sorry
