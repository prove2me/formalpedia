-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_past_infimum_from_dyadic_grid
-- name    : BellWilliams2001.ThresholdPolicy.past_infimum_from_dyadic_grid
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:37:42.455698+00:00
-- url     : https://prove2.me/theorems/2a273546-20b5-43dc-97bc-7af9e970733a
-- title:
--   The running infimum of a right-continuous path from a dyadic grid
-- statement:
--   The positive part of the difference between a path at time t and its minimum-so-far is the supremum of the corresponding differences over dyadic times capped at t.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem past_infimum_from_dyadic_grid (f : ℝ → ℝ) (t : ℝ≥0)
    (hRight : ∀ s : ℝ, 0 ≤ s → ContinuousWithinAt f (Ici s) s)
    (hBound : BddBelow (range (fun s : Icc (0 : ℝ) (t : ℝ) => f s))) :
    ENNReal.ofReal (f t - ⨅ s : Icc (0 : ℝ) (t : ℝ), f s) =
      ⨆ p : ℕ × ℕ, ENNReal.ofReal (f t - f (min t ((p.2 : ℝ≥0) / (2 : ℝ≥0)^p.1))) := by sorry

end BellWilliams2001.ThresholdPolicy
