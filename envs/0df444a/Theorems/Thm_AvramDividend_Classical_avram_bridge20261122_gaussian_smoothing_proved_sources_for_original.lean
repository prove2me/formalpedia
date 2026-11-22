-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_gaussian_smoothing_proved_sources_for_original
-- name    : AvramDividend.Classical.avram_bridge20261122_gaussian_smoothing_proved_sources_for_original
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T22:48:56.134802+00:00
-- url     : https://prove2.me/theorems/fba9a934-983d-4652-bd66-94e8e0c699eb
-- title:
--   Original stopped Gaussian source with one-sided mollification, slope certificate and finite-cap generator supersolution
-- statement:
--   Original stopped Gaussian source with one-sided mollification, slope certificate and finite-cap generator supersolution. The original source theorem process, dividend strategy, clock and cash/terminal conclusion remain intact. The conditional child imports published exact source lemmas. For the negative-mark model, generator identities require additional finite-measure negative support beyond the finite-activity hypothesis; the result remains restricted to that case. The missing original stochastic stopped budget stays Open.
-- source:
--   Actual connected Avram parent fdb9a6a3-8833-4d25-bb20-d197ce675232 and Proved original source heads d4ddb3b2-5b55-42a9-a4c3-30a4b5f7d2e8, 1d8fa7f6-b153-4240-9614-d0b1e281dc93

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bridge20261122_gaussian_smoothing_proved_sources_for_original
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
    (hGaussianSmoothingSources : (∀ (μ : Measure ℝ) (φ V g : ℝ → ℝ)
    (hφI : Integrable φ μ) (hφpos : 0 ≤ᵐ[μ] φ)
    (hφnorm : (∫ z, φ z ∂μ) = 1)
    (hPositive : ∀ᵐ z ∂μ, 0 < z)
    (ε : ℝ) (hε : 0 < ε) (b c : ℝ) (hc : 0 ≤ c)
    (hSec : ∀ x y : ℝ, x ≤ y → y - x ≤ V y - V x)
    (hg : ∀ u, g u ≤ if b < u then c else 0)
    (hVI : ∀ y, Integrable (fun z => φ z * V (y - ε*z)) μ)
    (hgI : ∀ y, Integrable (fun z => φ z * g (y - ε*z)) μ)
    (y : ℝ)
    (hDiff : DifferentiableAt ℝ
      (fun t => ∫ z, φ z * V (t - ε*z) ∂μ) y),
1 ≤ deriv (fun t => ∫ z, φ z * V (t - ε*z) ∂μ) y ∧
      (∫ z, φ z * g (y - ε*z) ∂μ) ≤
        if b < y then c else 0) ∧
      (∀ (μ : Measure ℝ) (φ g V : ℝ → ℝ)
    (hφI : Integrable φ μ) (hφpos : 0 ≤ᵐ[μ] φ)
    (hφnorm : (∫ z, φ z ∂μ) = 1)
    (hPositive : ∀ᵐ z ∂μ, 0 < z)
    (ε : ℝ) (hε : 0 < ε) (b y α : ℝ) (hα : 1 ≤ α)
    (hg : ∀ u : ℝ, g u ≤ if b < u then max X.c 0 else 0)
    (hgI : Integrable (fun z => φ z * g (y - ε*z)) μ)
    (hφkink : 0 ≤ φ ((y - b) / ε))
    (hWeak : X.generator
      (fun t => ∫ z, φ z * V (t - ε*z) ∂μ) y =
      (∫ z, φ z * g (y - ε*z) ∂μ) +
      X.σ ^ 2 / 2 * (1 - α) * φ ((y - b) / ε) / ε),
X.generator (fun t => ∫ z, φ z * V (t - ε*z) ∂μ) y ≤
      if b < y then max X.c 0 else 0)) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + R ω) := by sorry
