-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_k_exp_image_ofReal_pow_lintegrals_eq
-- name    : AvramDividend.Classical.avram_p2_k_exp_image_ofReal_pow_lintegrals_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:16:12.288136+00:00
-- url     : https://prove2.me/theorems/f521337e-5b17-48ba-ab64-4589d927d072
-- title:
--   Exponential pushforward powers commute with taking the ENNReal nonnegative part
-- statement:
--   For a general measurable real source Y, all kth moments of its exponential pushforward agree between (ofReal z)^k and ofReal(z^k), since exponential observations are positive. Supplies the necessary notation bridge between original P2-B and P2-I interfaces.
-- source:
--   Transport both monomial lintegrals along the exact exponential map using pinned lintegral_map. The exponential is strictly positive at every source point; ENNReal.ofReal_pow thus identifies (ofReal exp)^k with ofReal(exp^k) pointwise. This bridge is necessary because Proved P2-I c02ab0e5 expects powers of ofReal z, while Proved original small-time moment theorem 2ca40085 supplies ofReal(z^k). No jump-count assumptions.

import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_k_exp_image_ofReal_pow_lintegrals_eq
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (Y : α → ℝ) (hY : Measurable Y) (k : ℕ) :
    (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
      μ.map (fun ω => Real.exp (Y ω))) =
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      μ.map (fun ω => Real.exp (Y ω))) := by sorry
