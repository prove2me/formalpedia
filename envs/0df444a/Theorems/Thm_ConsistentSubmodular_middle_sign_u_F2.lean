-- Prove2me | Theorems.Thm_ConsistentSubmodular_middle_sign_u_F2
-- name    : ConsistentSubmodular.middle_sign_u_F2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:27.913202+00:00
-- url     : https://prove2.me/theorems/36689bb6-0a9b-49ea-8f61-90c0ed199f9e
-- title:
--   Positivity of $k^3+39k^2-153k+144$ on $[\tfrac74,2]$
-- statement:
--   For every real $k$ with $\tfrac74\le k\le 2$,
--   $$k^3+39k^2-153k+144>0.$$
--
--   This is a strict positivity (sign) fact for a cubic polynomial in the parameter $k$ on a compact interval. It is a certified elementary inequality used to fix the sign of a coefficient in the middle-parent credit analysis of the deterministic certificate construction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/MiddleSigns.lean#L123-L136 (`ConsistentSubmodular.middle_sign_u_F2`)

import Mathlib

theorem ConsistentSubmodular.middle_sign_u_F2 (k : ℝ) (hl : (7 / 4 : ℝ) ≤ k) (hu : k ≤ 2) :
    0 < k ^ 3 + 39 * k ^ 2 - 153 * k + 144 := by sorry
