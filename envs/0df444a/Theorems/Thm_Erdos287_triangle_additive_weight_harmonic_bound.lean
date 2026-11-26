-- Prove2me | Theorems.Thm_Erdos287_triangle_additive_weight_harmonic_bound
-- name    : Erdos287.triangle_additive_weight_harmonic_bound
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:07:36.931878+00:00
-- url     : https://prove2.me/theorems/cf7cfec4-268f-4042-81ae-97b411b1dacd
-- title:
--   Harmonic bound for the additive parameters of a triangle
-- statement:
--   For every natural number $B$, $\sum_{1\le u,v\le B}(u+v)^{-2}\le\sum_{1\le u\le B}u^{-1}$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.triangle_additive_weight_harmonic_bound (B : ℕ) :
    (∑ i ∈ Finset.range B, ∑ j ∈ Finset.range B, (1 : ℚ) / ((i : ℚ) + j + 2) ^ 2)
      ≤ ∑ i ∈ Finset.range B, (1 : ℚ) / ((i : ℚ) + 1) := by sorry
