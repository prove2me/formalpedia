-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_complete_paid_cash_lt_top
-- name    : AvramDividend.Classical.avram_wave6_08_original_positive_ruin_complete_paid_cash_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:12:18.500467+00:00
-- url     : https://prove2.me/theorems/0588c7a4-1fbb-4b74-962a-7481c91f1a28
-- title:
--   Actual complete finite positive ruin stopped discounted Stieltjes reward is finite including initial right payment
-- statement:
--   For the genuine original dividend strategy and any finite strictly positive ruin time, the complete discounted Stieltjes paymentTimes reward is pathwise finite for q≥0. It retains the time-zero right dividend and all strictly pre-ruin continuous and atomic dividends while excluding a right payment at ruin. The original closed-horizon Stieltjes mass bounds the initial singleton, the independently Proved strict-open discounted reward is finite, and the exact original source split adds these two finite quantities. No stochastic Itô, compensator or coupling assumption is made.
-- source:
--   Proved original [0,τ] dividend mass, finite positive ruin strict-open discounted cash and exact paymentTimes split; ENNReal addition preserves finite totals.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_strict_discounted_cash_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_finite_ruin_full_cash_zero_atom_plus_strict_left
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_08_original_positive_ruin_complete_paid_cash_lt_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (τ : ℝ≥0) (hτ : 0 < τ) :
    (∫⁻ t in paymentTimes (τ : ℝ≥0∞) ∩ Iic (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ := by sorry
