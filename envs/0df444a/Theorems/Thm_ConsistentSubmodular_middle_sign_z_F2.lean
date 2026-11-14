-- Prove2me | Theorems.Thm_ConsistentSubmodular_middle_sign_z_F2
-- name    : ConsistentSubmodular.middle_sign_z_F2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:48.742698+00:00
-- url     : https://prove2.me/theorems/42807ccf-1ec7-4c97-9e4c-fe667ff2ddc7
-- title:
--   Positivity of $20k^3-62k^2+33k+27$ on $[\tfrac74,2]$
-- statement:
--   For every real $k$ with $\tfrac74\le k\le 2$,
--   $$20k^3-62k^2+33k+27>0.$$
--
--   This is a strict positivity (sign) fact for a cubic polynomial in the parameter $k$ on a compact interval. It is a certified elementary inequality used to fix the sign of a coefficient in the middle-parent credit analysis of the deterministic certificate construction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/MiddleSigns.lean#L214-L227 (`ConsistentSubmodular.middle_sign_z_F2`)

import Mathlib

theorem ConsistentSubmodular.middle_sign_z_F2 (k : ℝ) (hl : (7 / 4 : ℝ) ≤ k) (hu : k ≤ 2) :
    0 < 20 * k ^ 3 - 62 * k ^ 2 + 33 * k + 27 := by sorry
