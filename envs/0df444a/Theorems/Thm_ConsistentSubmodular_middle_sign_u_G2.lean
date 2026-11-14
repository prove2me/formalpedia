-- Prove2me | Theorems.Thm_ConsistentSubmodular_middle_sign_u_G2
-- name    : ConsistentSubmodular.middle_sign_u_G2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:28.511134+00:00
-- url     : https://prove2.me/theorems/d09b2145-3657-4306-9b8d-6120c2956e2b
-- title:
--   Positivity of $-3k^3-27k^2+236k-288$ on $[\tfrac74,2]$
-- statement:
--   For every real $k$ with $\tfrac74\le k\le 2$,
--   $$-3k^3-27k^2+236k-288>0.$$
--
--   This is a strict positivity (sign) fact for a cubic polynomial in the parameter $k$ on a compact interval. It is a certified elementary inequality used to fix the sign of a coefficient in the middle-parent credit analysis of the deterministic certificate construction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/MiddleSigns.lean#L93-L106 (`ConsistentSubmodular.middle_sign_u_G2`)

import Mathlib

theorem ConsistentSubmodular.middle_sign_u_G2 (k : ℝ) (hl : (7 / 4 : ℝ) ≤ k) (hu : k ≤ 2) :
    0 < -3 * k ^ 3 - 27 * k ^ 2 + 236 * k - 288 := by sorry
