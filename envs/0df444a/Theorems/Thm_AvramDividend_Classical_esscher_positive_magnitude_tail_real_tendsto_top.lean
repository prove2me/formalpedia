-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_positive_magnitude_tail_real_tendsto_top
-- name    : AvramDividend.Classical.esscher_positive_magnitude_tail_real_tendsto_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:28:01.401824+00:00
-- url     : https://prove2.me/theorems/940a0338-8628-44b7-8b31-1ef8e4c2c136
-- title:
--   Infinite negative activity forces infinite Esscher-weighted positive jump-magnitude tail
-- statement:
--   Transfer divergent signed negative Lévy-jump tail intensity through an Esscher weight to the positive jump-magnitude strict-tail kernel, for every nonnegative Esscher root. Finite unweighted truncated tails imply finite weighted truncated tails; the canonical signed-to-magnitude identity completes the transfer. This is the precise kernel appearing in the BV Esscher renewal representation.
-- source:
--   Composition of Proved theorems esscher_weighted_negative_tail_le_unweighted (25fe0eaf), esscher_weighted_negative_tail_real_tendsto_top_of_small_band (3c0fe1fa) and esscher_weighted_signed_jump_tail_map_identity (33ba13f8).

import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_le_unweighted
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_real_tendsto_top_of_small_band
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_signed_jump_tail_map_identity
import Mathlib.MeasureTheory.Measure.WithDensity

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- The explicit positive jump-magnitude Esscher tail diverges at the origin under infinite unweighted negative-tail activity. -/
theorem esscher_positive_magnitude_tail_real_tendsto_top
    (ν : Measure ℝ) (φ : ℝ) (hφ : 0 ≤ φ)
    (hfar : ν (Iic (-1 : ℝ)) < ⊤)
    (hfinite : ∀ x : ℝ, 0 < x → ν (Iio (-x)) < ⊤)
    (htail : Tendsto (fun x : ℝ => (ν (Iio (-x))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    Tendsto (fun x : ℝ =>
      (((ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
        (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
        {z : ℝ≥0 | x < (z : ℝ)}).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by sorry

end AvramDividend.Classical
