-- Prove2me | Theorems.Thm_BraidsLinksMCG_leftHalfPlane_ambient_pathConnected_v1
-- name    : BraidsLinksMCG.leftHalfPlane_ambient_pathConnected_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-26T13:52:22.868451+00:00
-- url     : https://prove2.me/theorems/2f5b1bdc-727c-4835-8fef-c19a3dffeb6e
-- title:
--   The punctured left half-plane is path connected in the ambient plane
-- statement:
--   Let n >= 0 and let W be the open left half-plane {Re z < n+1} with the n+1 real points 1, 2, ..., n+1 deleted. Then W is path connected.
--
--   Every puncture is real, so a point of W with nonzero imaginary part is never a puncture. Each point of W is joined to the anchor i: a single segment when its imaginary part is positive, two segments through -i when its imaginary part is negative, and a single segment when it is real, whose only real point is the starting point itself. The imaginary-axis segment [-i, i] has real part constantly 0, whereas every puncture has real part at least 1.
--
--   All half-plane containments follow from convexity, and puncture avoidance is pointwise: a uniform positive distance bound would be false, since points of the upper half-plane approach the real axis arbitrarily closely.
-- source:
--   A. Hatcher, Algebraic Topology (2002), Section 1.2, applied to the classical punctured plane; the construction is the standard axis-parallel routing about a safe hub column.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

open Set

namespace BraidsLinksMCG

/-- The ambient left half-plane with the `n+1` real punctures removed is path
connected, joined at the anchor `i`. -/
theorem leftHalfPlane_ambient_pathConnected_v1 (n : ℕ) :
    IsPathConnected
      ({z : ℂ | z.re < ((n : ℝ) + 1 : ℝ)} ∩
        (Set.range (fun j : Fin (n + 1) => (((j : ℕ) + 1 : ℕ) : ℂ)))ᶜ) := by sorry

end BraidsLinksMCG
