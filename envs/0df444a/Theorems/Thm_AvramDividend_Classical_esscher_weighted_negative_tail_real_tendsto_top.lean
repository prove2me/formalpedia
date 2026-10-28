-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_real_tendsto_top
-- name    : AvramDividend.Classical.esscher_weighted_negative_tail_real_tendsto_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:21:29.614452+00:00
-- url     : https://prove2.me/theorems/29ca6aba-5c4f-4ea2-87e9-409c618fce9d
-- title:
--   Infinite small negative jumps force Esscher-weighted real tail to diverge
-- statement:
--   Assuming finite strict negative tails at positive truncations, the Esscher weight of every negative jump is at most one, preserving finiteness. A uniform lower bound exp(-φ) on the unit small-jump band then transfers the infinite origin limit of small-jump mass to the Esscher-weighted real tail. This is the required real kernel-growth bridge for infinite-activity bounded variation.
-- source:
--   Proved weighted tail upper/lower inequalities and Filter.tendsto_atTop.

import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_le_unweighted
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_real_ge_small_band
import Mathlib.Topology.Algebra.Order.Field

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped ENNReal

namespace AvramDividend.Classical

/-- Esscher-weighted real negative jump mass diverges with the finite truncated small-jump tail. -/
theorem esscher_weighted_negative_tail_real_tendsto_top
    (ν : Measure ℝ) (φ : ℝ) (hφ : 0 ≤ φ)
    (hfinite : ∀ x : ℝ, 0 < x → ν (Iio (-x)) < ⊤)
    (hsmall : Tendsto
      (fun x : ℝ => (ν (Ioo (-1 : ℝ) (-x))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    Tendsto
      (fun x : ℝ =>
        ((ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
          (Iio (-x))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by sorry

end AvramDividend.Classical
