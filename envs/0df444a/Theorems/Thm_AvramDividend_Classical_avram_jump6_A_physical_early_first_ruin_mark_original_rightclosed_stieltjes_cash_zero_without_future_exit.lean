-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_physical_early_first_ruin_mark_original_rightclosed_stieltjes_cash_zero_without_future_exit
-- name    : AvramDividend.Classical.avram_jump6_A_physical_early_first_ruin_mark_original_rightclosed_stieltjes_cash_zero_without_future_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:36:40.963256+00:00
-- url     : https://prove2.me/theorems/f6fb9d22-c951-4580-8b09-2de381aedf07
-- title:
--   Physical size-two Poisson first-mark Brownian tube forces original inclusive stopped cash zero without future exit
-- statement:
--   For a true original Brownian−2N spectrally-negative Lévy physical sample path, if its Brownian component remains within 1/4000 until σ, then the original finite cap barrier starting at x=1/10 and paying at a=1/5 makes zero cumulative dividends up to and including σ. By the exact original right-closed Stieltjes mass identity for any cap x≤a, dividendMeasure(Iic σ)=ENNReal.ofReal(Dσ)=0, which forces the original discounted ruin-clipped Iic cash integral to vanish. Unlike previous source 23271938 this does not assume existence of any finite future upper exit. It supplies the genuinely local, source-faithful physical reward calculation needed for a positive probability early marked ruin sample-path countermodel to the unit-mark Ito ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_physical_early_first_ruin_mark_original_rightclosed_stieltjes_cash_zero_without_future_exit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B : ℝ≥0 → ℝ) (N : ℝ≥0 → ℕ)
    (σ : ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (q : ℝ) :
    (∫⁻ s in paymentTimes
        (ruinTime X (1 / 10 : ℝ)
          (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω) ∩
        Iic (σ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)) = 0 := by sorry
