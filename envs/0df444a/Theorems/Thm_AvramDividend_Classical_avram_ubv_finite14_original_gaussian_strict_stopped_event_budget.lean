-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite14_original_gaussian_strict_stopped_event_budget
-- name    : AvramDividend.Classical.avram_ubv_finite14_original_gaussian_strict_stopped_event_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-09T07:59:33.657362+00:00
-- url     : https://prove2.me/theorems/47a4991e-13cf-4dc9-9d8c-99412b7431de
-- title:
--   Original finite-cap Gaussian strict stopped reward eventwise HJB budget
-- statement:
--   The strictly prepayment Gaussian stopped C2 reward, including exact zero-clock branch and original strict Stieltjes cash, has expected value over each event of the original initial filtration at most w(x) times that event's probability. This isolates the genuinely stochastic original-X/D Ito-Meyer and localisation step needed by Open c31f81c8, whose measure-theoretic conversion is now Proved 9904a1e6.
-- source:
--   Necessary physical stopped Gaussian eventwise budget child of selected Open c31f81c8; uses no independent filtration or surrogate Brownian process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite14_original_gaussian_strict_stopped_event_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
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
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A,
        (if σ k ω = 0 then w x else
          Real.exp (-(q * (σ k ω : ℝ))) *
            w (riskProcess X x D (σ k ω) ω) +
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal) ∂P) ≤
          w x * (P A).toReal := by sorry
