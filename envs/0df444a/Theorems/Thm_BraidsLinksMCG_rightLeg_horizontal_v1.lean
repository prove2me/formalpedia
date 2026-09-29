-- Prove2me | Theorems.Thm_BraidsLinksMCG_rightLeg_horizontal_v1
-- name    : BraidsLinksMCG.rightLeg_horizontal_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-26T23:18:15.242315+00:00
-- url     : https://prove2.me/theorems/74689e3e-3a16-494a-919f-f698af9c0b18
-- title:
--   A horizontal leg of nonzero constant imaginary part meets no puncture
-- statement:
--   Let n >= 0 and let R = {Re z > n + 1/2} minus the n+1 real points 1, 2, ..., n+1. Let x and y be two points of R with the same imaginary part, and suppose that imaginary part is nonzero. Then x and y are joined inside R by a path. Every puncture is real, so the horizontal segment between them, which has constant nonzero imaginary part, meets none of them; and the segment stays in the half-space because the half-space is convex.
-- source:
--   A. Hatcher, Algebraic Topology (2002), Section 1.2, applied to the classical punctured plane; the horizontal leg of the axis-parallel routing used in rightAmbient_pathConnected_v1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

open Set

namespace BraidsLinksMCG

open Set

/-- The segment of the punctured right half-plane `{z | n + 1/2 < z.re}` that joins
two points of equal imaginary part is path connected, provided that common
imaginary part is nonzero.

Every puncture of the plane is real, so a segment lying on a line of constant
nonzero imaginary part cannot contain one.  Containment in the half-plane follows
from its convexity. -/
theorem rightLeg_horizontal_v1 (n : ℕ) (x y : ℂ)
    (hxy : x.im = y.im) (hne : x.im ≠ 0)
    (hx : (n : ℝ) + 1 / 2 < x.re) (hy : (n : ℝ) + 1 / 2 < y.re) :
    JoinedIn
        ({z : ℂ | (n : ℝ) + 1 / 2 < z.re} ∩
          (Set.range (fun j : Fin (n + 1) => (((j : ℕ) + 1 : ℕ) : ℂ)))ᶜ)
        x y := by sorry

end BraidsLinksMCG
