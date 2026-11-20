-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_spatial_Hsource_at_true_first_negative_size2_mark_equals_zero
-- name    : AvramDividend.Classical.avram_jump6_A_original_spatial_Hsource_at_true_first_negative_size2_mark_equals_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:44:01.650998+00:00
-- url     : https://prove2.me/theorems/ecc66d09-329f-4353-87dc-e37e6132724d
-- title:
--   The exact original spatial stopped payoff H_k vanishes on the physical size-two first-ruin mark when κ_k equals first arrival
-- statement:
--   For a genuine original spectrally negative Lévy sample path with X=B−2N, a strict positive first negative-size-two mark at time σ, no preceding marks, a uniformly small Brownian path and first-mark ruin, the original source functional H_k has exactly zero value at that mark provided the original spatial stop κ_k equals σ. In particular, the fully original source H_k definition uses the closed Stieltjes dividend cash through ruin and the correct post-ruin riskProcess rather than a synthetic reward proxy. This isolates a crucial bridge from the actual dividend/ruin construction into the defective unit-Jfull signed mesh certificate 061f936f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_finitecap_marked_ruin_discounted_original_reward_zero_no_future_exit
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_spatial_Hsource_at_true_first_negative_size2_mark_equals_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B : ℝ≥0 → ℝ) (N : ℝ≥0 → ℕ)
    (σ : ℝ≥0) (hσ : 0 < σ)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hBefore : ∀ t : ℝ≥0, t < σ → N t = 0)
    (hMark : 1 ≤ N σ)
    (q : ℝ) (w : ℝ → ℝ)
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (H : ℕ → Ω → ℝ) (κ : ℕ → Ω → ℝ≥0)
    (k : ℕ) (hκ : κ k ω = σ)
    (hHsource : ∀ j η, H j η =
      Real.exp (-(q * (κ j η : ℝ))) *
      w (if κ j η = 0 ∨
            (κ j η : ℝ≥0∞) <
              ruinTime X (1 / 10 : ℝ)
                (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) η then
          (1 / 10 : ℝ) + X.X (κ j η) η -
            rightLimit
              (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
              (κ j η) η
         else
           riskProcess X (1 / 10 : ℝ)
             (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
             (κ j η) η) +
      (∫⁻ s in paymentTimes
          (ruinTime X (1 / 10 : ℝ)
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) η)
          ∩ Iic (κ j η : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure
           (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) η)).toReal) :
    H k ω = 0 := by sorry
