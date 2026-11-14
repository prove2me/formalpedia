-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat05_ubv_positive_core_minimal_429e
-- name    : AvramDividend.Classical.avram_wave6_chat05_ubv_positive_core_minimal_429e
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T23:43:57.230198+00:00
-- url     : https://prove2.me/theorems/f6b58900-32e0-4639-bef2-697c677c3916
-- title:
--   Minimal UBV positive-initial core for corrected 429e (definitions-only)
-- statement:
--   Minimal strictly-positive-reserve UBV verification core isolating the 0<x branch of corrected 429e17ca. Same hypotheses and discounted Stieltjes conclusion as the existing positive-initial core, republished as a definitions-only child so the corrected parent sketch has a small reduction graph. Zero case and admissibility nonnegativity are handled separately at the parent.
-- source:
--   Exact positive-branch restriction of authoritative corrected UBV core 429e17ca-5528-40b5-b593-7c03973d0706: assume 0<x (hence 0<C) with all parent generator/gradient/jump hypotheses; conclusion is the authentic expected discounted full Stieltjes dividend inequality. Derived by case split on initial capital using Proved b3117b07 (0<=x) and Proved 14599b22 (x=0). No model or hypothesis changed; publication asserts no graph edge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_chat05_ubv_positive_core_minimal_429e
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
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
