-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_ruinclipped_finite_barrier_Hsource_zero_at_exact_negative_ruin
-- name    : AvramDividend.Classical.avram_jump6_A_original_ruinclipped_finite_barrier_Hsource_zero_at_exact_negative_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:53:05.203724+00:00
-- url     : https://prove2.me/theorems/d001b4c0-59b5-4291-9280-5f65a155fbaf
-- title:
--   Original discounted ruin-clipped finite-barrier stopped cash source is zero at exact negative first-ruin contact
-- statement:
--   For the original actual finite barrierStrategy, at a strictly positive stopping clock σ equal to the true original ruinTime, if riskProcess at that clock is negative and the inclusive stopped discounted Stieltjes cash is zero, then the exact Hsource in the disputed original physical unit-fullmark cash theorem equals zero. The negative risk chooses the post-ruin branch of its own ruin-clipped terminal value w(riskProcess)=0 and zero dividends. This proves the original stopped payoff identity conditional on true ruin contact without introducing synthetic payoff or martingale sources.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_ruinclipped_finite_barrier_Hsource_zero_at_exact_negative_ruin
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a q : ℝ) (w : ℝ → ℝ)
    (hNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (ω : Ω) (σ : ℝ≥0) (hPos : 0 < σ)
    (hExact : (σ : ℝ≥0∞) =
      ruinTime X x (barrierStrategy X x a) ω)
    (hRuin : riskProcess X x (barrierStrategy X x a) σ ω < 0)
    (hCash :
      (∫⁻ s in paymentTimes (ruinTime X x (barrierStrategy X x a) ω)
          ∩ Iic (σ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure (barrierStrategy X x a) ω)) = 0)
    (H : ℝ)
    (hSource : H =
      Real.exp (-(q * (σ : ℝ))) *
        w (if σ = 0 ∨
              (σ : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω then
          x + X.X σ ω - rightLimit (barrierStrategy X x a) σ ω
        else riskProcess X x (barrierStrategy X x a) σ ω) +
      (∫⁻ s in paymentTimes (ruinTime X x (barrierStrategy X x a) ω)
          ∩ Iic (σ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure (barrierStrategy X x a) ω)).toReal) :
    H = 0 := by sorry
