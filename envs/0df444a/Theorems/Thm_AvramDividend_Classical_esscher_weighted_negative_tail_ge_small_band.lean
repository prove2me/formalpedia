-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_ge_small_band
-- name    : AvramDividend.Classical.esscher_weighted_negative_tail_ge_small_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:42:23.028848+00:00
-- url     : https://prove2.me/theorems/071ceda0-a852-4fdf-bb6b-8dc08aa499f9
-- title:
--   Esscher-weighted negative Lévy tail dominates discounted small-jump band mass
-- statement:
--   For a nonnegative Esscher parameter, the exponential weight exp(phi*y) on signed negative jumps between -1 and -x is at least exp(-phi). Therefore the weighted strict negative-jump tail dominates exp(-phi) times the unweighted small-jump band mass. This measure-level comparison is the main missing quantitative input for infinite-activity BV scale-derivative divergence.
-- source:
--   Set-valued lower bound for the Lebesgue integral of an ENNReal density, iInf_mul_le_setLIntegral, and exp monotonicity from pinned Mathlib.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

open MeasureTheory Set
open scoped ENNReal

namespace AvramDividend.Classical

/-- On the unit negative-jump band, Esscher discounting has a uniform positive floor. -/
theorem esscher_weighted_negative_tail_ge_small_band
    (ν : Measure ℝ) (φ x : ℝ) (hφ : 0 ≤ φ) :
    ENNReal.ofReal (Real.exp (-φ)) * ν (Ioo (-1 : ℝ) (-x)) ≤
      (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
        (Iio (-x)) := by sorry

end AvramDividend.Classical
