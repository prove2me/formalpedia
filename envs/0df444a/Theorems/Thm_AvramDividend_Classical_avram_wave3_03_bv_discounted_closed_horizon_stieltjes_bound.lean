-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
-- name    : AvramDividend.Classical.avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:43:16.315988+00:00
-- url     : https://prove2.me/theorems/899a15ee-29a7-4820-b5c7-d87109a699fe
-- title:
--   Entire discounted actual dividend Stieltjes mass on a closed finite horizon, including continuous payments and right terminal jumps, is bounded by the post-payment cumulative dividend
-- statement:
--   For the actual adapted, monotone, left-continuous dividend process D, every nonnegative discount rate and every nonnegative horizon, the full discounted Stieltjes integral on the closed interval [0,T] is bounded by the strict-right cumulative dividend limit. All continuous and singular-continuous payment mass, the right jump at time zero and the terminal right jump are included. No countable-jump concentration is invoked.
-- source:
--   Combine Proved discounted_stieltjes_lintegral_le_measure with Proved avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit; the set [0,T] is Borel and nonnegative.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_lintegral_le_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    (∫⁻ t in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal (rightLimit D T ω) := by sorry
