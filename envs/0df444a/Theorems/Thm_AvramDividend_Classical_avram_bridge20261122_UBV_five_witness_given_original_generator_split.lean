-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_UBV_five_witness_given_original_generator_split
-- name    : AvramDividend.Classical.avram_bridge20261122_UBV_five_witness_given_original_generator_split
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T21:09:49.732785+00:00
-- url     : https://prove2.me/theorems/e9f7c7f9-5451-4098-9ce4-4d118284f051
-- title:
--   Original UBV stopped five-witness Ito inequality given true Gaussian and marked-jump generator split
-- statement:
--   The full source-faithful five-witness stopped original UBV inequality with the actual stopped terminal and discounted dividend Stieltjes cash. The only additional premise is the authentic generator integral decomposition into Gaussian and Lévy negative-mark parts on each measurable predictable set when those two parts are integrable. The remaining hard obligation is a true stopped Ito-Meyer physical-martingale residual budget.
-- source:
--   Exact original P4-F Open target fdb9a6a3 with Gaussian/negative mark source split from Proved 30a96e81. The latter imports five verified theorems including its pointwise generator splitting identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bridge20261122_UBV_five_witness_given_original_generator_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
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
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P) 
    (hSourceGeneratorSplit : ∀ (T : ℝ≥0)
          (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
          (E : Set (ℝ≥0 × Ω))
          (hE : MeasurableSet[𝓕.rightCont.predictable] E)
          (hG : IntegrableOn
            (fun p : ℝ≥0 × Ω => (if p.1 ≤ T then
                Real.exp (-(q * (p.1 : ℝ))) *
                  (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
              else 0) *
              (X.σ ^ 2 / 2 * iteratedDeriv 2 w
                  (Function.leftLim
                  (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1))) E μ)
          (hJ : IntegrableOn
            (fun p : ℝ≥0 × Ω => (if p.1 ≤ T then
                Real.exp (-(q * (p.1 : ℝ))) *
                  (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
              else 0) *
              (X.c * deriv w (Function.leftLim
                  (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) +
                   (∫ z in Iio (0 : ℝ),
                     SpectrallyNegativeLevy.generatorIntegrand w (Function.leftLim
                  (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) z ∂X.ν) -
                   q * w (Function.leftLim
                  (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1))) E μ),
          (∫ p in E, (if p.1 ≤ T then
                Real.exp (-(q * (p.1 : ℝ))) *
                  (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
              else 0) *
            (X.generator w (Function.leftLim
                  (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) - q * w (Function.leftLim
                  (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)) ∂μ) =
          (∫ p in E, (if p.1 ≤ T then
                Real.exp (-(q * (p.1 : ℝ))) *
                  (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
              else 0) *
            (X.σ ^ 2 / 2 * iteratedDeriv 2 w
                  (Function.leftLim
                  (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)) ∂μ) +
          (∫ p in E, (if p.1 ≤ T then
                Real.exp (-(q * (p.1 : ℝ))) *
                  (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
              else 0) *
            (X.c * deriv w (Function.leftLim
                  (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) +
                   (∫ z in Iio (0 : ℝ),
                     SpectrallyNegativeLevy.generatorIntegrand w (Function.leftLim
                  (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) z ∂X.ν) -
                   q * w (Function.leftLim
                  (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)) ∂μ)
    ) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + R ω)  := by sorry
