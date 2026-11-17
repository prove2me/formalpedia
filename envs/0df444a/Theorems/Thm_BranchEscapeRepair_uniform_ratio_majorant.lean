-- Prove2me | Theorems.Thm_BranchEscapeRepair_uniform_ratio_majorant
-- name    : BranchEscapeRepair.uniform_ratio_majorant
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T15:23:42.270986+00:00
-- url     : https://prove2.me/theorems/a2ba2c6b-61d7-4fa3-afd9-8da1dbf2e71d
-- title:
--   Uniform summable majorant for power ratios
-- statement:
--   For every natural n≥2, positive real x≤n and positive d, (x/(x+d))^n≤4/d².
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandão Bueno. Repair of Section 3 of On the Infinitude of Off-Critical Zeros (April 2026). Elementary inequality; no novelty claim.

import Mathlib

theorem BranchEscapeRepair.uniform_ratio_majorant (n : ℕ) (hn : 2 ≤ n) (x d : ℝ) (hx : 0 < x) (hxn : x ≤ n) (hd : 0 < d) : (x / (x+d))^n ≤ 4 / d^2 := by sorry
