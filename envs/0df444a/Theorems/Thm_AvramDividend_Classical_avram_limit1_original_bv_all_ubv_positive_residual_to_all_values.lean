-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_original_bv_all_ubv_positive_residual_to_all_values
-- name    : AvramDividend.Classical.avram_limit1_original_bv_all_ubv_positive_residual_to_all_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:20:35.012536+00:00
-- url     : https://prove2.me/theorems/74643374-dd7c-4052-8cf6-19b0c06c2343
-- title:
--   Canonical-shaped BV all-reserve and UBV positive-reserve residuals yield full capped/top verification
-- statement:
--   The original P3 bounded-variation source obligations are formulated for x≥0, whereas the original P4 Itô-Meyer source obligation fdb9a6a3/0dda1be7 assumes x>0. This root-facing adapter asks for genuine residual witnesses only when X.BoundedVariation or x>0. The Proved original all-variation source preflight constructs the exact τ,W,Cash,Term at k>0; the all-variation residual-to-full dividendValue lemma handles those signed integrable source witnesses and preserves the first right-payment atom by n+1 and Iic. For UBV at x=0, import Proved avram_limit1_ubv_zero_actual_dividendValue_le and its source-exact right-payment argument. HJB entails the gradient floor. Finally pass original admissible strategy bounds to valueFunctionLe and the C=top unrestricted valueFunction by the Proved local verification supremum lemma. No martingale source is assumed silently, no terminal vanishing, no equality in law.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_original_bv_all_ubv_positive_residual_to_all_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (hResidual : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      (X.BoundedVariation ∨ 0 < x) →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ k : ℕ, 0 < k →
      ∀ (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ),
      (∀ ω, τ ω =
        (min (ruinTime X x D ω) (k : ℝ≥0∞)).toNNReal) →
      (∀ ω, W ω = if τ ω = 0 ∨
        (τ ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
        else riskProcess X x D (τ ω) ω) →
      (∀ ω, Cash ω = (∫⁻ s in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) →
      (∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) →
      ∃ M G H : Ω → ℝ,
        Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
        (∫ ω, M ω ∂P) = 0 ∧
        (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
        (∀ᵐ ω ∂P, Term ω + Cash ω ≤
          w x + M ω + G ω + H ω)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
