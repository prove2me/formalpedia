-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin24_original_finite_cap_event_ito_mean_only
-- name    : AvramDividend.Classical.avram_mix_fin24_original_finite_cap_event_ito_mean_only
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T11:09:14.677246+00:00
-- url     : https://prove2.me/theorems/2545e563-477d-44a7-be66-58697aa9ebad
-- title:
--   Finite-cap original bounded stopped mixed Ito event mean inequality
-- statement:
--   This is exactly the original finite mixed original-process expected stopped HJB cash and postpayment terminal inequality from Open 5fe19fc9 with the independently Proved nonnegative initial reward cb38fe6d removed. Requires a genuine finite-activity Gaussian-plus-negative-jump stopped Itô and eventwise budget, handling initial and terminal atoms. Do not assume unjustified global L1 MG+MJ or separate auxiliary Brownian.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin24_original_finite_cap_event_ito_mean_only
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
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
    (n : ℕ) (hn : 0 < n)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCfinite : C ≠ ⊤)
    (σk : ℕ → Ω → ℝ≥0)
    (hσkle : ∀ k ω, σk k ω ≤ σ ω)
    (hσkstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σk k ω : WithTop ℝ≥0)))
    (Fk : ℕ → Ω → ℝ)
    (hFksource : ∀ k ω, Fk k ω =
          Real.exp (-(q * (σk k ω : ℝ))) *
            w (if σk k ω = 0 ∨
                  (σk k ω : ℝ≥0∞) < ruinTime X x D ω then
                x + X.X (σk k ω) ω - rightLimit D (σk k ω) ω
              else riskProcess X x D (σk k ω) ω) +
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σk k ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal) :
    ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      ∀ k : ℕ,
        (∫ ω in A ∩ {ω : Ω | σk k ω ≠ 0}, Fk k ω ∂P) ≤
          w x * (P (A ∩ {ω : Ω | σ ω ≠ 0})).toReal := by sorry
