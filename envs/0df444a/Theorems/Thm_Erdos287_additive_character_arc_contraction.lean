-- Prove2me | Theorems.Thm_Erdos287_additive_character_arc_contraction
-- name    : Erdos287.additive_character_arc_contraction
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:09:42.653814+00:00
-- url     : https://prove2.me/theorems/694158cf-bfe4-45c6-bd78-0bcf98e88b9f
-- title:
--   Quadratic contraction of an additive character away from zero phase
-- statement:
--   Let $q>0$ and let $v$ be the representative in $[0,q-1]$ of $x\in\mathbb Z/q\mathbb Z$. For the standard additive character $\chi$, one has $|1+\chi(x)|\le2\exp(-2d^2)$ where $d=\min(v/q,1-v/q)$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.additive_character_arc_contraction (q : ℕ) [NeZero q] (x : ZMod q) :
    ‖(1 : ℂ) + ZMod.stdAddChar x‖ ≤
      2 * Real.exp (-2 * (min ((x.val : ℝ) / q) (1 - (x.val : ℝ) / q)) ^ 2) := by sorry
