-- Prove2me | Theorems.Thm_ConsistentSubmodular_middle_sign_z_Nplus
-- name    : ConsistentSubmodular.middle_sign_z_Nplus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:25.785213+00:00
-- url     : https://prove2.me/theorems/c2934aac-5dfb-40b3-93c3-d56b56d1d70a
-- title:
--   Positivity of $118k^3-695k^2+1081k-378$ on $[\tfrac43,\tfrac74]$
-- statement:
--   For every real $k$ with $\tfrac43\le k\le \tfrac74$,
--   $$118k^3-695k^2+1081k-378>0.$$
--
--   This is a strict positivity (sign) fact for a cubic polynomial in the parameter $k$ on a compact interval. It is a certified elementary inequality used to fix the sign of a coefficient in the middle-parent credit analysis of the deterministic certificate construction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/MiddleSigns.lean#L138-L151 (`ConsistentSubmodular.middle_sign_z_Nplus`)

import Mathlib

theorem ConsistentSubmodular.middle_sign_z_Nplus (k : ℝ) (hl : (4 / 3 : ℝ) ≤ k) (hu : k ≤ (7 / 4 : ℝ)) :
    0 < 118 * k ^ 3 - 695 * k ^ 2 + 1081 * k - 378 := by sorry
