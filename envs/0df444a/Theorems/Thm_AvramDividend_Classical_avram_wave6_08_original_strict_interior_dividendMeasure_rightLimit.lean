-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_strict_interior_dividendMeasure_rightLimit
-- name    : AvramDividend.Classical.avram_wave6_08_original_strict_interior_dividendMeasure_rightLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:48:11.622229+00:00
-- url     : https://prove2.me/theorems/cd71bccf-bc9e-4e72-b68d-dde85a1f5b56
-- title:
--   Original full Stieltjes strictly interior mass equals prepayment terminal less postpayment initial reserve
-- statement:
--   For every genuine left-continuous, nondecreasing dividend strategy on the original probability space, the full Stieltjes mass strictly between two ordered nonnegative times equals the cumulative dividend before payment at the terminal time minus the postpayment right limit at the initial time. Thus right-side atoms at both endpoints are excluded, including a possible right payment at the ruin instant; singular-continuous and atomic interior dividends are included.
-- source:
--   Exact source-specific half-open Stieltjes mass and right-atom identity; measure-theoretic disjoint decomposition, no stochastic assumptions or substitute law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_eq_dividend_increment
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave6_08_original_strict_interior_dividendMeasure_rightLimit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) (hab : a < b) :
    dividendMeasure D ω (Ioo (a : ℝ) (b : ℝ)) =
      ENNReal.ofReal (D b ω - rightLimit D a ω) := by sorry
