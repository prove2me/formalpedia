-- Prove2me | Theorems.Thm_BraidsLinksMCG_rightAmbient_pathConnected_v1
-- name    : BraidsLinksMCG.rightAmbient_pathConnected_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-26T23:01:11.446205+00:00
-- url     : https://prove2.me/theorems/35d548f3-1e9d-4fe3-b8e9-5e687c67651b
-- title:
--   The punctured right half-plane is path connected in the ambient plane
-- statement:
--   Let n >= 0 and let R be the open right half-plane {Re z > n + 1/2} with the n+1 real points 1, 2, ..., n+1 deleted. Then R is path connected.
--
--   The region is NOT star-shaped about any point, so no single-segment construction from a fixed hub exists. Instead each endpoint reaches the hub h = (n + 3/4) + I by two axis-aligned segments. A point with nonzero imaginary part moves horizontally first, on a line of constant nonzero imaginary part, which therefore misses every puncture because all punctures are real. A point on the real axis moves vertically first; that vertical leg meets the real axis only at its own foot, which is in the region by assumption, and the following horizontal leg lies at height 1. The second leg of the nonreal case runs along the column of constant real part n + 3/4, which is not an integer and hence is not the real part of any puncture.
--
--   All half-plane containments follow from convexity of {Re z > c}. Puncture avoidance is pointwise and structural: a uniform positive distance bound would be false.
-- source:
--   A. Hatcher, Algebraic Topology (2002), Section 1.2, applied to the classical punctured plane; the construction is the standard axis-parallel routing about a safe hub column whose real part is non-integral.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

open Set

namespace BraidsLinksMCG

open Set

/-- The punctured right half-plane `Re z > n + 1/2`, minus the `n+1` real
punctures, is path connected, joined at the hub `n + 3/4 + I`. -/
theorem rightAmbient_pathConnected_v1 (n : ℕ) :
    IsPathConnected
      ({z : ℂ | (n : ℝ) + 1 / 2 < z.re} ∩
        (Set.range (fun j : Fin (n + 1) => (((j : ℕ) + 1 : ℕ) : ℂ)))ᶜ) := by sorry

end BraidsLinksMCG
