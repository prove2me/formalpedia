-- Prove2me | Theorems.Thm_ConsistentSubmodular_middle_sign_z_F1
-- name    : ConsistentSubmodular.middle_sign_z_F1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:46.678742+00:00
-- url     : https://prove2.me/theorems/1b6300f3-ebb3-49a4-8c37-dc15d315f484
-- title:
--   Positivity of $35k^3-104k^2+60k+27$ on $[\tfrac74,2]$
-- statement:
--   For every real $k$ with $\tfrac74\le k\le 2$,
--   $$35k^3-104k^2+60k+27>0.$$
--
--   This is a strict positivity (sign) fact for a cubic polynomial in the parameter $k$ on a compact interval. It is a certified elementary inequality used to fix the sign of a coefficient in the middle-parent credit analysis of the deterministic certificate construction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/MiddleSigns.lean#L199-L212 (`ConsistentSubmodular.middle_sign_z_F1`)

import Mathlib

theorem ConsistentSubmodular.middle_sign_z_F1 (k : ℝ) (hl : (7 / 4 : ℝ) ≤ k) (hu : k ≤ 2) :
    0 < 35 * k ^ 3 - 104 * k ^ 2 + 60 * k + 27 := by sorry
