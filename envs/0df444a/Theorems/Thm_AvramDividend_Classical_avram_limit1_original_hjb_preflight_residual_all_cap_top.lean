-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_original_hjb_preflight_residual_all_cap_top
-- name    : AvramDividend.Classical.avram_limit1_original_hjb_preflight_residual_all_cap_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:20:33.836194+00:00
-- url     : https://prove2.me/theorems/75649d41-f34b-4b05-8522-57fe76a71e60
-- title:
--   Original stopped preflight plus sole residual obligation yields all BV/UBV capped/top value bounds
-- statement:
--   The public accepted all-BV/UBV preflight 0cbba3ce constructs genuine finite clipped ruin stopping clocks, their real measurability, correct τ=0 and postpayment W branch, right-closed discounted Stieltjes Cash, integrability of Cash, and discounted Term. For each x≥0, admissible D and positive k, the ONLY missing information supplied here is a genuinely original-process integrable centred stochastic residual with signed nonpositive HJB drift; this is an explicit hResidual hypothesis with original W/Cash/Term equalities. Feed these witnesses into the new all-variation positive-horizon LIMIT-1 value theorem and recover capped valueFunctionLe and C=top unrestricted valueFunction for all x≥0. This integrates the actual zero/right atom without terminal vanishing or equality in law, and does not misrepresent P3/P4 stochastic work as proved.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_original_hjb_preflight_residual_all_cap_top
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
