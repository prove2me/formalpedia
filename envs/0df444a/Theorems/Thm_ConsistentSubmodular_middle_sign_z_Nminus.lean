-- Prove2me | Theorems.Thm_ConsistentSubmodular_middle_sign_z_Nminus
-- name    : ConsistentSubmodular.middle_sign_z_Nminus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:28.408788+00:00
-- url     : https://prove2.me/theorems/ce32ed24-af03-4535-8f32-d167b2ffdaef
-- title:
--   Positivity of $-160k^4+1196k^3-2494k^2+702k+1512$ on $[\tfrac43,\tfrac74]$
-- statement:
--   For every real $k$ with $\tfrac43\le k\le \tfrac74$,
--   $$-160k^4+1196k^3-2494k^2+702k+1512>0.$$
--
--   This is a strict positivity (sign) fact for a quartic polynomial in the parameter $k$ on a compact interval. It is a certified elementary inequality used to fix the sign of a coefficient in the middle-parent credit analysis of the deterministic certificate construction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/MiddleSigns.lean#L153-L167 (`ConsistentSubmodular.middle_sign_z_Nminus`)

import Mathlib

theorem ConsistentSubmodular.middle_sign_z_Nminus (k : ℝ) (hl : (4 / 3 : ℝ) ≤ k) (hu : k ≤ (7 / 4 : ℝ)) :
    0 < -160 * k ^ 4 + 1196 * k ^ 3 - 2494 * k ^ 2 + 702 * k + 1512 := by sorry
