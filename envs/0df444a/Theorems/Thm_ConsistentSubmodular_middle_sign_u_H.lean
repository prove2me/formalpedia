-- Prove2me | Theorems.Thm_ConsistentSubmodular_middle_sign_u_H
-- name    : ConsistentSubmodular.middle_sign_u_H
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:30.283103+00:00
-- url     : https://prove2.me/theorems/16368d8f-e8b7-4d90-ab5d-5231be249af6
-- title:
--   Positivity of the polynomial $k^3+4k^2-51k+72$ on $[\tfrac{38}{23},\tfrac74]$
-- statement:
--   For every real $k$ with $\tfrac{38}{23}\le k\le \tfrac74$,
--   $$k^3+4k^2-51k+72>0.$$
--
--   This is a strict positivity (sign) fact for a cubic polynomial in the parameter $k$ on a compact interval. It is a certified elementary inequality used to fix the sign of a coefficient in the middle-parent credit analysis of the deterministic certificate construction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/MiddleSigns.lean#L33-L46 (`ConsistentSubmodular.middle_sign_u_H`)

import Mathlib

theorem ConsistentSubmodular.middle_sign_u_H (k : ℝ) (hl : (38 / 23 : ℝ) ≤ k) (hu : k ≤ (7 / 4 : ℝ)) :
    0 < k ^ 3 + 4 * k ^ 2 - 51 * k + 72 := by sorry
