-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_uniform_prefix_physical_hjb_budget
-- name    : AvramDividend.Classical.avram_ubv_top9_original_uniform_prefix_physical_hjb_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-07T10:58:31.333904+00:00
-- url     : https://prove2.me/theorems/cac4feee-b211-4347-82e3-2ccde99a9ab1
-- title:
--   Original bounded-prefix physical UBV Ito-Meyer stopped HJB expected budgets at all compact local clocks
-- statement:
--   Exact original source positive-clock Gaussian, compensated small/large jumps, discounted Stieltjes dividend and ruin/cemetery accounting for every true right-continuous local clock whose entire preceding Levy path is bounded by j+1. This is weaker than the existing endpoint-only arbitrary-clock budget, enabling honest predictable compact C2 control.
-- source:
--   Proved 90b203a8 upcross prefix; Proved 72000b1a strict pre-ruin compact strip once certified; Proved ca1e7b57 Gaussian HJB energy and f16 finite-mesh centred terms. Physical Ito identity remains an explicit open obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_uniform_prefix_physical_hjb_budget
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
    (hFI : ∀ k, Integrable (F k) P) (hinfinite : C = ⊤) :
    ∀ k, ∀ (κ : ℕ → Ω → ℝ≥0)
      (hκstop : ∀ j, IsStoppingTime 𝓕.rightCont
        (fun ω => (κ j ω : WithTop ℝ≥0)))
      (hκle : ∀ j ω, κ j ω ≤ σ k ω)
      (hκprefix : ∀ j ω (t : ℝ≥0), t ≤ κ j ω → X.X t ω ≤ (j : ℝ) + 1)
      (H : ℕ → Ω → ℝ),
      (∀ j ω, H j ω =
        Real.exp (-(q * (κ j ω : ℝ))) *
          w (if κ j ω = 0 ∨ (κ j ω : ℝ≥0∞) < ruinTime X x D ω then
              x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
            else riskProcess X x D (κ j ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) →
      ∀ j, (∫ ω, H j ω ∂P) ≤ w x := by sorry
