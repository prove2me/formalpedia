-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_circle_reciprocal_distance_bound
-- name    : BirkhoffGlobalSection.circle_reciprocal_distance_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T07:34:55.807916+00:00
-- url     : https://prove2.me/theorems/dc1d5576-d02c-4fe5-9ce6-40a2fa8163bb
-- title:
--   Reciprocal-distance bound on a circle inside the primaries
-- statement:
--   For a circle of radius 0<r<1 about the left primary and any horizontal relative coordinate a between -r and r, the increase of the reciprocal distance to the right primary from that point to the nearest point on the circle is at least r-a. This is an elementary inequality for the inverse-square-root distance.
-- source:
--   Elementary inverse-distance estimate for the circular restricted three-body effective potential of Joung--van Koert equation (1.1), https://arxiv.org/abs/2407.19159v3.

import Mathlib

namespace BirkhoffGlobalSection

/-- A reciprocal-distance bound along a circle of radius less than the primary separation. -/
theorem circle_reciprocal_distance_bound (r a : ℝ)
    (hr : 0 < r) (hr1 : r < 1)
    (ha_lo : -r ≤ a) (ha_hi : a ≤ r) :
    r - a ≤ 1 / (1 - r) -
      1 / Real.sqrt (1 + r ^ 2 - 2 * a) := by sorry

end BirkhoffGlobalSection
