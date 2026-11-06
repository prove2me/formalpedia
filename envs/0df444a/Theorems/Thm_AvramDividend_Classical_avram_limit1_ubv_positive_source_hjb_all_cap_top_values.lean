-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_ubv_positive_source_hjb_all_cap_top_values
-- name    : AvramDividend.Classical.avram_limit1_ubv_positive_source_hjb_all_cap_top_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:24:25.567063+00:00
-- url     : https://prove2.me/theorems/f12c6db9-ac20-4989-bf40-b871ba42deb7
-- title:
--   Original UBV HJB and positive source martingales certify all capped and unrestricted values
-- statement:
--   Source-exact unbounded-variation local verification under the original positive discount, nonnegative boundary value, negative-zero extension, interior C2 smoothness and nonlinear generator HJB max-equals-zero premises. Require original clipped finite positive ruin-clock W/Cash/Term and centred signed residual martingale certificates only for strictly positive reserves, with all source measurability and integrability explicit. The independently Proved HJB decomposition yields the derivative floor. The independently Proved positive-source LIMIT-1 passage yields actual dividendValue bounds for positive reserves, while the accepted exact zero-reserve LIMIT-1 proof handles x=0. The accepted positive-to-all-values lemma then yields every capped and C=top unrestricted value function upper bound. No zero-reserve stochastic certificate, equality-in-law, assumption of terminal vanishing or import from canonical open P4 verification.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_implies_components
import Theorems.Thm_AvramDividend_Classical_avram_limit1_ubv_positive_and_zero_to_all_values
import Theorems.Thm_AvramDividend_Classical_avram_limit1_ubv_uniform_positive_source_to_dividendValue

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_ubv_positive_source_hjb_all_cap_top_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (hEvidence : ∀ x : ℝ, 0 < x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ k : ℕ, 0 < k →
      ∃ (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ),
        (∀ ω, τ ω =
          (min (ruinTime X x D ω) (k : ℝ≥0∞)).toNNReal) ∧
        Measurable (fun ω => (τ ω : ℝ)) ∧
        (∀ ω, W ω = if τ ω = 0 ∨
          (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) ∧
        (∀ ω, Cash ω = (∫⁻ s in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal) ∧
        (∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) ∧
        Integrable Cash P ∧
        (∃ M G H : Ω → ℝ,
          Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
          (∫ ω, M ω ∂P) = 0 ∧
          (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
          (∀ᵐ ω ∂P, Term ω + Cash ω ≤
            w x + M ω + G ω + H ω))) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
