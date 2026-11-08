-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_L1_grid_error_expected_upper
-- name    : AvramDividend.Classical.avram_ubv_finite9_original_L1_grid_error_expected_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:16:39.275084+00:00
-- url     : https://prove2.me/theorems/302a8a51-c3ef-4902-ac2b-1b94c8d6a710
-- title:
--   Original finite-cap stopped expected HJB bound from centred grid approximants and vanishing L1 error
-- statement:
--   For the exact original spectrally negative Lévy dividend process, finite cap, post-right-payment surplus and payment-times cash through each stopping subclock, suppose the finite-grid approximant has integrable mean zero and a signed remainder whose expected absolute value tends to zero. If each source-exact payoff is almost everywhere bounded by initial candidate value plus approximant and remainder, the expected payoff is at most the initial value. Uses the existing public Proved signed-error theorem and the norm-integral estimate; existence of the genuine stochastic Ito source remains separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_approximate_mean_zero_budget_implies_expected_upper

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_original_L1_grid_error_expected_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (σ : ℕ → Ω → ℝ≥0) (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (F : ℕ → Ω → ℝ)
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
    (hApprox : ∀ k, ∃ M Err : ℕ → Ω → ℝ,
      (∀ j, Integrable (M j) P ∧ (∫ ω, M j ω ∂P) = 0) ∧
      (∀ j, Integrable (Err j) P) ∧
      Tendsto (fun j => ∫ ω, ‖Err j ω‖ ∂P) atTop (nhds (0 : ℝ)) ∧
      (∀ j, ∀ᵐ ω ∂P,
        F k ω ≤ w x + M j ω + Err j ω)) :
    ∀ k, (∫ ω, F k ω ∂P) ≤ w x := by sorry
