-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_outer_inverse_distance_potential_min
-- name    : BirkhoffGlobalSection.outer_inverse_distance_potential_min
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:26:28.033626+00:00
-- url     : https://prove2.me/theorems/a00fdda9-3278-4ed6-b0e4-0e05e41c05d9
-- title:
--   Minimum of a two-centre outer effective potential
-- statement:
--   For nonnegative weights A and B and positive radii u and v, if u satisfies the stationary equation for the outer potential (r+a)^2/2+A/r+B/(1+r), then its potential value is at most the value at v. This follows from the positive quadratic remainders of all three convex summands.
-- source:
--   Elementary real inequality obtained from the inverse-distance effective potential associated with Joung--van Koert equation (1.1), https://arxiv.org/abs/2407.19159v3.

import Mathlib

namespace BirkhoffGlobalSection

/-- The unique stationary point of the strictly convex outer effective potential is its minimum. -/
theorem outer_inverse_distance_potential_min
    (a A B u v : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : 0 < u) (hv : 0 < v)
    (hbal : u + a = A / u ^ 2 + B / (1 + u) ^ 2) :
    (u + a) ^ 2 / 2 + A / u + B / (1 + u) ≤
      (v + a) ^ 2 / 2 + A / v + B / (1 + v) := by sorry

end BirkhoffGlobalSection
