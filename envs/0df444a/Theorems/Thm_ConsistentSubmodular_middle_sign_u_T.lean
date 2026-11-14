-- Prove2me | Theorems.Thm_ConsistentSubmodular_middle_sign_u_T
-- name    : ConsistentSubmodular.middle_sign_u_T
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:27.548266+00:00
-- url     : https://prove2.me/theorems/4f4a33cb-a078-43da-8c63-f134bad2a553
-- title:
--   Positivity of $-7k^3+187k^2-822k+912$ on $[\tfrac{38}{23},\tfrac74]$
-- statement:
--   For every real $k$ with $\tfrac{38}{23}\le k\le \tfrac74$,
--   $$-7k^3+187k^2-822k+912>0.$$
--
--   This is a strict positivity (sign) fact for a cubic polynomial in the parameter $k$ on a compact interval. It is a certified elementary inequality used to fix the sign of a coefficient in the middle-parent credit analysis of the deterministic certificate construction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/MiddleSigns.lean#L63-L76 (`ConsistentSubmodular.middle_sign_u_T`)

import Mathlib

theorem ConsistentSubmodular.middle_sign_u_T (k : ℝ) (hl : (38 / 23 : ℝ) ≤ k) (hu : k ≤ (7 / 4 : ℝ)) :
    0 < -7 * k ^ 3 + 187 * k ^ 2 - 822 * k + 912 := by sorry
