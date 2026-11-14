-- Prove2me | Theorems.Thm_ConsistentSubmodular_middle_sign_u_G1
-- name    : ConsistentSubmodular.middle_sign_u_G1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:29.502289+00:00
-- url     : https://prove2.me/theorems/b7d27862-8f1d-474b-b54c-2be066478975
-- title:
--   Positivity of $-3k^3-42k^2+319k-360$ on $[\tfrac74,2]$
-- statement:
--   For every real $k$ with $\tfrac74\le k\le 2$,
--   $$-3k^3-42k^2+319k-360>0.$$
--
--   This is a strict positivity (sign) fact for a cubic polynomial in the parameter $k$ on a compact interval. It is a certified elementary inequality used to fix the sign of a coefficient in the middle-parent credit analysis of the deterministic certificate construction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/MiddleSigns.lean#L78-L91 (`ConsistentSubmodular.middle_sign_u_G1`)

import Mathlib

theorem ConsistentSubmodular.middle_sign_u_G1 (k : ℝ) (hl : (7 / 4 : ℝ) ≤ k) (hu : k ≤ 2) :
    0 < -3 * k ^ 3 - 42 * k ^ 2 + 319 * k - 360 := by sorry
