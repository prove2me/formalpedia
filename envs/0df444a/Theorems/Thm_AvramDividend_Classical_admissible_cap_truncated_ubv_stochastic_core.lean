-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_ubv_stochastic_core
-- name    : AvramDividend.Classical.admissible_cap_truncated_ubv_stochastic_core
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T20:54:59.268599+00:00
-- url     : https://prove2.me/theorems/ab47d6d9-7cd8-4e6a-b5b9-00d29941d9d4
-- title:
--   Unbounded-variation stochastic verification core after dividend-jump control
-- statement:
--   This is the unbounded-variation stochastic-calculus core of Proposition 4(i) after all discrete dividend-jump algebra has already been discharged. It assumes the nonpositive generator drift, w'≥1 for the continuous dividend component, explicit control of every admissible right-jump of D by the verification-function drop, and nonnegativity of the stopped terminal term. The remaining proof is the C2 Lévy Itô/localisation/expectation argument.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), unbounded-variation branch of Section 5.4 leading to (5.13). This child starts after the deterministic HJB and dividend-jump inequalities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissible_cap_truncated_ubv_stochastic_core
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
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
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
