-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_finitecap_marked_ruin_discounted_original_reward_zero_no_future_exit
-- name    : AvramDividend.Classical.avram_jump6_A_actual_finitecap_marked_ruin_discounted_original_reward_zero_no_future_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:38:05.834919+00:00
-- url     : https://prove2.me/theorems/9e8fb7a3-82ce-4dd9-ade0-4cffd4156d6f
-- title:
--   The true original stopped finite-cap terminal and inclusive cash reward vanishes at first negative mark without future-exit assumptions
-- statement:
--   For the actual original finite-cap spectrally negative Lévy path X=B−2N, with the Brownian tube up to σ, no negative Poisson count before σ and at least one size-two mark at σ, the true ruinTime equals σ and the exact discounted w(riskProcess) terminal plus original right-closed Stieltjes dividend cash at σ is zero. The proof uses the already Proved exact original first negative-mark ruin clock a48667b3 and strict negative reserve dfe5cb52 together with the new cumulative Stieltjes mass source 6b2ed43a and its no-future-exit physical cash corollary f6fb9d22. No future finite upcrossing clock u is required, so the statement applies to every physical first marked ruin event satisfying the tube, including those for which the negative-drift Brownian-Poisson path never crosses the upper barrier subsequently.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_actual_finitecap_marked_ruin_discounted_original_reward_zero_no_future_exit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B : ℝ≥0 → ℝ) (N : ℝ≥0 → ℕ)
    (σ : ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hBefore : ∀ t : ℝ≥0, t < σ → N t = 0)
    (hMark : 1 ≤ N σ)
    (w : ℝ → ℝ) (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (q : ℝ) :
    ruinTime X (1 / 10 : ℝ)
      (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω =
        (σ : ℝ≥0∞) ∧
    Real.exp (-(q * (σ : ℝ))) *
      w (riskProcess X (1 / 10 : ℝ)
          (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) σ ω) +
      (∫⁻ s in paymentTimes
          (ruinTime X (1 / 10 : ℝ)
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω) ∩
          Iic (σ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure
              (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)).toReal = 0 := by sorry
