-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_spatial_all_Hk_zero_at_physical_first_mark_with_true_clipped_ruin_clock
-- name    : AvramDividend.Classical.avram_jump6_A_original_spatial_all_Hk_zero_at_physical_first_mark_with_true_clipped_ruin_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:52:41.62588+00:00
-- url     : https://prove2.me/theorems/f4bba85a-8fea-46d7-9821-e4ddf36f197f
-- title:
--   Original ruin-truncated spatial stopped H_k is exactly zero at every original spatial level on the true first negative two mark
-- statement:
--   For a genuine spectrally negative Lévy process X=B−2N with its real negative size-two Poisson first mark at σ>0, no previous marks and a small Brownian tube until σ≤1/500, take the original barrier x=1/10, cap C=1/5, the authentic horizon-one ruin-truncated physical stopping clock ρ=min(ruinTime,1), and the original upper-exit spatial localisation κ_k=min(ρ,twoSidedExitUpTime(k+1)). The previously Proved exact first-ruin clock identity gives κ_k=σ at every k. The original Hsource uses the inclusive Stieltjes cash and the post-ruin risk value; the previously Proved physical first-ruin Hsource lemma makes H_k=0 at every k. This closes the exact original first-ruin stopped reward interpretation across all its spatial localisations, establishing a core component of the suspected unit-Jfull certificate counterexample.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_ruin_truncated_spatial_clock_equals_first_size2_mark_all_k
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_spatial_Hsource_at_true_first_negative_size2_mark_equals_zero
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_spatial_all_Hk_zero_at_physical_first_mark_with_true_clipped_ruin_clock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B : ℝ≥0 → ℝ) (N : ℝ≥0 → ℕ)
    (σ : ℝ≥0) (hσ : 0 < σ)
    (hSmall : (σ : ℝ) ≤ 1 / 500)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hBefore : ∀ t : ℝ≥0, t < σ → N t = 0)
    (hMark : 1 ≤ N σ)
    (q : ℝ) (w : ℝ → ℝ)
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (H : ℕ → Ω → ℝ) (ρ : Ω → ℝ≥0)
    (κ : ℕ → Ω → ℝ≥0)
    (hρ : ρ ω =
      (min (ruinTime X (1 / 10 : ℝ)
        (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)
        (1 : ℝ≥0∞)).toNNReal)
    (hκ : ∀ j, κ j ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((j : ℝ) + 1) ω)).toNNReal)
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
    ∀ k : ℕ, H k ω = 0 := by sorry
