-- Prove2me | Theorems.Thm_ConsistentSubmodular_middle_sign_u_Q
-- name    : ConsistentSubmodular.middle_sign_u_Q
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:30.48149+00:00
-- url     : https://prove2.me/theorems/b1c409d3-73bd-4a09-b75d-970a653be51c
-- title:
--   Positivity of $-k^3-19k^2+134k-144$ on $[\tfrac{38}{23},\tfrac74]$
-- statement:
--   For every real $k$ with $\tfrac{38}{23}\le k\le \tfrac74$,
--   $$-k^3-19k^2+134k-144>0.$$
--
--   This is a strict positivity (sign) fact for a cubic polynomial in the parameter $k$ on a compact interval. It is a certified elementary inequality used to fix the sign of a coefficient in the middle-parent credit analysis of the deterministic certificate construction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/MiddleSigns.lean#L48-L61 (`ConsistentSubmodular.middle_sign_u_Q`)

import Mathlib

theorem ConsistentSubmodular.middle_sign_u_Q (k : ℝ) (hl : (38 / 23 : ℝ) ≤ k) (hu : k ≤ (7 / 4 : ℝ)) :
    0 < -k ^ 3 - 19 * k ^ 2 + 134 * k - 144 := by sorry
