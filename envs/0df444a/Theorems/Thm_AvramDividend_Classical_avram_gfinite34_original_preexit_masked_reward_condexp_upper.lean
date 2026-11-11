-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite34_original_preexit_masked_reward_condexp_upper
-- name    : AvramDividend.Classical.avram_gfinite34_original_preexit_masked_reward_condexp_upper
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T10:04:19.237934+00:00
-- url     : https://prove2.me/theorems/aaf8aec2-a49b-4545-aae6-ee9cc54b884e
-- title:
--   Original finite-cap Gaussian pre-exit stopped strict reward admits an initial conditional budget
-- statement:
--   For the original zero-jump spectrally negative Levy process, original admissible dividend strategy and each genuine bounded ruin-clipped pre-exit stopping clock with positive reserve floor, the original discounted postpayment terminal plus strict pre-ruin cash, masked by its true value w(x) at a zero clock, has conditional expectation at initial time at most w(x). Requires original-process stopped Ito–Stieltjes source, Gaussian centring, cap/zero-contact and endpoint handling. The reward is integrable from existing Proved theorem avram_gfinite28_original_bounded_stop_masked_strict_reward_L1.
-- source:
--   Only remaining analytic conditional-budget step for existing public Open 7f7d661b-6a89-4b7f-9eed-d7d356111a2a. The parent is reduced via existing Proved reward L1 and conditional-centred witness lemmas, with a source-exact event integral calculation. No stochastic source is assumed elsewhere.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gfinite34_original_preexit_masked_reward_condexp_upper
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
        δ ≤ riskProcess X x D t ω),
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P (fun η =>
          if ρ η = 0 then w x else
            Real.exp (-(q * (ρ η : ℝ))) *
              w (riskProcess X x D (ρ η) η) +
            (∫⁻ s in paymentTimes (ruinTime X x D η) ∩ Iio (ρ η : ℝ),
              ENNReal.ofReal (Real.exp (-(q * s)))
              ∂(dividendMeasure D η)).toReal) ω ≤ w x := by sorry
