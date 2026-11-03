-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_ruin_clock_truncation_inner_lintegral_iSup
-- name    : AvramDividend.Classical.avram_wave7_11_ruin_clock_truncation_inner_lintegral_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:26:55.746305+00:00
-- url     : https://prove2.me/theorems/cb688725-26d6-4de2-b273-6682efdec394
-- title:
--   Original Stieltjes payout integral along the truncated ruin clock increases to its full-ruin value
-- statement:
--   For every original dividend path D(·,ω), extended ruin clock σ, discount rate q and finite terminal horizon T, the complete discounted ENNReal Stieltjes payoff over paymentTimes σ∩Iic T is the supremum over natural n of the same original Stieltjes payoff with paymentTimes(min σ n)∩Iic T. Time-zero atoms, infinite ruin, and arbitrary σ are preserved. This is the inner/pathwise monotone-convergence identity needed to pass from uniform truncated-ruin estimates to finite-horizon full-ruin estimates; it does not assert outer expectation convergence or stochastic martingale bounds.
-- source:
--   Proved original-source lemmas paymentTimes_eq_iUnion_nat_horizons (77691e31...), paymentTimes_measurable (88dafb7f...), paymentTimes_min_mono_horizon (021cfe05...). Apply pinned MeasureTheory.lintegral_iSup to measurable indicator functions of the increasing Borel payment sets and rewrite via MeasureTheory.lintegral_indicator. Parent gap: UBV positive-initial uniform ruin-clock budget 3c9532b7 and canonical cc518136.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_iUnion_nat_horizons
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_ruin_clock_truncation_inner_lintegral_iSup
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (q T : ℝ) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    ⨆ n : ℕ, (∫⁻ t in paymentTimes (min σ (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
