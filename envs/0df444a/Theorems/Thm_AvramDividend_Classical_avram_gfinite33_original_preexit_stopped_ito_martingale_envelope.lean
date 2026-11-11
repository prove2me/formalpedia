-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite33_original_preexit_stopped_ito_martingale_envelope
-- name    : AvramDividend.Classical.avram_gfinite33_original_preexit_stopped_ito_martingale_envelope
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T08:01:33.172448+00:00
-- url     : https://prove2.me/theorems/7f7d661b-6a89-4b7f-9eed-d7d356111a2a
-- title:
--   Source-exact finite-cap Gaussian stopped Itô cash inequality with an initially centred martingale envelope
-- statement:
--   For the same original zero-negative-jump Levy X and admissible D and exactly the original positive-floor stopped clock rho, construct an integrable source martingale residual on the original initial event with vanishing event integral. The original discounted postpayment terminal plus strict pre-ruin Stieltjes cash is pointwise dominated almost surely by w(x) plus that residual. The true Gaussian finite-grid predictable centring, generator and gradient signs, finite-cap contact, time-zero right payment, physical stopped mesh convergence, and ruin/horizon endpoint are all obligations of this child; no surrogate Gaussian space, implicit independent Brownian construction, or arbitrary-grid claim is allowed. This is the substantive stochastic component isolated from event-integral algebra.
-- source:
--   Necessary stochastic ledger child of original finite-cap stopped C2 event budget 6eb9cc6a. The parent is reduced using the separate generic Proved eventwise integral comparison and original capped reward L1. This child must be proved with a constructive original-X/D stopped Ito–Stieltjes certificate, not by importing any parent or assuming a reward inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gfinite33_original_preexit_stopped_ito_martingale_envelope
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
    ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ ω : WithTop ℝ≥0)))
      (hρle : ∀ ω, ρ ω ≤ σ k ω)
      (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      ∃ M : Ω → ℝ,
        IntegrableOn M (A ∩ {η : Ω | ρ η ≠ 0}) P ∧
        (∫ ω in A ∩ {η : Ω | ρ η ≠ 0}, M ω ∂P) = 0 ∧
        (∀ᵐ ω ∂(P.restrict (A ∩ {η : Ω | ρ η ≠ 0})),
          (Real.exp (-(q * (ρ ω : ℝ))) *
              w (riskProcess X x D (ρ ω) ω) +
            (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
              ENNReal.ofReal (Real.exp (-(q * s)))
              ∂(dividendMeasure D ω)).toReal) ≤ w x + M ω) := by sorry
