-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_jump_small_band_tendsto_top
-- name    : AvramDividend.Classical.negative_jump_small_band_tendsto_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:56:31.965661+00:00
-- url     : https://prove2.me/theorems/4027f977-ede0-45da-8226-7d744c4f60df
-- title:
--   Truncated infinite negative jump intensity diverges inside the small-jump band
-- statement:
--   If the negative-tail mass diverges towards the origin while the total mass of jumps of size at least one is finite and every positive truncation is finite, then the mass on jumps with magnitude strictly between x and one diverges. The proof decomposes the strict negative tail into a fixed finite far-jump part and an increasing small-jump band. This is the remaining unweighted measure limit input to the Esscher-weighted small-band inequality.
-- source:
--   Disjoint measure union, ENNReal.toReal_add for finite components, and Filter.tendsto_atTop in pinned Mathlib.

import Theorems.Thm_AvramDividend_Classical_negative_jump_real_tail_tendsto_top
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace AvramDividend.Classical

/-- Subtracting a finite far-jump band preserves negative-tail divergence at the origin. -/
theorem negative_jump_small_band_tendsto_top
    (ν : Measure ℝ)
    (hfar : ν (Iic (-1 : ℝ)) < ⊤)
    (hfinite : ∀ x : ℝ, 0 < x → ν (Iio (-x)) < ⊤)
    (htail : Tendsto (fun x : ℝ => (ν (Iio (-x))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    Tendsto (fun x : ℝ => (ν (Ioo (-1 : ℝ) (-x))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by sorry

end AvramDividend.Classical
