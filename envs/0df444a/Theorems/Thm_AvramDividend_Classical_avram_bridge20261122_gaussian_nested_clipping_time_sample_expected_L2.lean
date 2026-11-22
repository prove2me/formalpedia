-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_gaussian_nested_clipping_time_sample_expected_L2
-- name    : AvramDividend.Classical.avram_bridge20261122_gaussian_nested_clipping_time_sample_expected_L2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T22:58:49.247593+00:00
-- url     : https://prove2.me/theorems/2a97fa53-21fb-4d6a-9753-c69b5e4d3b86
-- title:
--   Original UBV stopped Ito residual with proved real-time and physical-law Gaussian nested-clipping expected error control
-- statement:
--   Same physical stopped Ito X,D and reward with a source-authentic integrated nested Gaussian clipping-error inequality, specialising the original alpha time-index measure to nonnegative time and beta sample-space measure to original P. Source theorem is already Proved; child remains responsible for genuine physical integrability, localisation and Ito residual.
-- source:
--   Original root-connected public Open fdb9a6a3 and exact Proved Gaussian nested clipping head 3e5de7fd, reaching all five underlying original source proofs.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bridge20261122_gaussian_nested_clipping_time_sample_expected_L2
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
    (hNestedClipping : (∀ (μ : Measure ℝ≥0) (w : ℝ → ℝ) (a a' b' b B q : ℝ)
    (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b)
    (hB : 1 ≤ B)
    (hgrad : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ B)
    (hq : 0 ≤ q)
    (Y : ℝ≥0 → Ω → ℝ) (t : ℝ≥0 → ℝ) (ht : ∀ s, 0 ≤ t s),
let G : ℝ≥0 → Ω → ℝ := fun s ω =>
      (Real.exp (-(q * t s)) *
          (if Y s ω ∈ Set.Icc a b then deriv w (Y s ω) else 1) -
        Real.exp (-(q * t s)) *
          (if Y s ω ∈ Set.Icc a' b' then deriv w (Y s ω) else 1))^2
    let J : ℝ≥0 → Ω → ℝ := fun s ω =>
      4 * B^2 *
        (if Y s ω ∈ Set.Icc a a' ∨ Y s ω ∈ Set.Icc b' b
          then (1 : ℝ) else 0)
    (∀ s, Integrable (G s) P) →
    (∀ s, Integrable (J s) P) →
    Integrable (fun s => ∫ ω, G s ω ∂P) μ →
    Integrable (fun s => ∫ ω, J s ω ∂P) μ →
    (∫ s, (∫ ω, G s ω ∂P) ∂μ) ≤
      (∫ s, (∫ ω, J s ω ∂P) ∂μ))) :
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
