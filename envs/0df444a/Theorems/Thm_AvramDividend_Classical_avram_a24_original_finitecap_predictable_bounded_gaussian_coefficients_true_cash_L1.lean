-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_original_finitecap_predictable_bounded_gaussian_coefficients_true_cash_L1
-- name    : AvramDividend.Classical.avram_a24_original_finitecap_predictable_bounded_gaussian_coefficients_true_cash_L1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T17:53:50.199805+00:00
-- url     : https://prove2.me/theorems/8665862c-43c2-4971-9361-44d9944225f1
-- title:
--   Original finite-cap physical bounded predictable Gaussian Ito Stieltjes cash positive L1 source
-- statement:
--   The missing original Gaussian Ito-Stieltjes source for the true finite-cap dividend verification problem. Construct, for the exact original clipped uniform stopped Gaussian grid, globally bounded a.e. strongly measurable adapted first-derivative and Hessian coefficients, yielding true finite-grid Gaussian linear and variance-compensated quadratic gains. Prove that the positive part of the original discounted post-right-dividend stopped payoff plus inclusive Stieltjes dividend cash minus the initial HJB value and physical Gaussian noise has expectation tending to zero. The already kernel-Proved conditional stopped Brownian first and second moments and bounded-coefficient integrability mean this child needs no duplicate integrability conclusions. The hard remaining task is to prove genuine pathwise Ito-Stieltjes Taylor and finite-cap kink/local-time, discounted singular dividend and ruin-endpoint L1 error estimates, not to assume them or replace the process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a24_original_finitecap_predictable_bounded_gaussian_coefficients_true_cash_L1
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
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hν : X.ν = 0) (hFinite : C ≠ ⊤) :
    ∀ k,
      let S : ℕ → Finset ℕ := fun j => Finset.range (j + 1)
      let τg : ℕ → ℕ → Ω → ℝ≥0 := fun j i ω =>
        min ((i : ℝ≥0) * ((n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0))) (σ k ω)
      let h : ℕ → ℕ → ℝ≥0 := fun j _ =>
        (n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
      ∀ (hτg : ∀ j, ∀ i ∈ S j, ∀ s : ℝ≥0,
        MeasurableSet[𝓕.rightCont s] {ω : Ω | τg j i ω ≤ s}),
      let M : ℕ → ℕ → Ω → ℝ := fun j i ω =>
        X.X (τg j i ω + h j i) ω - X.X (τg j i ω) ω -
          (h j i : ℝ) * X.c
      ∃ (G H : ℕ → ℕ → Ω → ℝ)
        (BG BH : ℕ → ℕ → ℝ),
      (∀ j i (hi : i ∈ S j),
        Measurable[(isStoppingTime_withTop_of_le_events (τg j i)
          (hτg j i hi)).measurableSpace] (G j i)) ∧
      (∀ j i (hi : i ∈ S j),
        Measurable[(isStoppingTime_withTop_of_le_events (τg j i)
          (hτg j i hi)).measurableSpace] (H j i)) ∧
      (∀ j i, AEStronglyMeasurable (G j i) P) ∧
      (∀ j i, AEStronglyMeasurable (H j i) P) ∧
      (∀ j i, ∀ᵐ ω ∂P, ‖G j i ω‖ ≤ BG j i) ∧
      (∀ j i, ∀ᵐ ω ∂P, ‖H j i ω‖ ≤ BH j i) ∧
      Tendsto (fun j => ∫ ω,
        max (F k ω - w x - (∑ i ∈ S j,
          (G j i ω * M j i ω +
            (H j i ω * (M j i ω)^2 -
              (h j i : ℝ) * X.σ^2 * H j i ω)))) 0 ∂P)
        atTop (nhds (0 : ℝ)) := by sorry
