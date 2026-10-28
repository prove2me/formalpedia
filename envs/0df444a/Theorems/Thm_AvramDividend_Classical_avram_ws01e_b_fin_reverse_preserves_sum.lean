-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fin_reverse_preserves_sum
-- name    : AvramDividend.Classical.avram_ws01e_b_fin_reverse_preserves_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T07:53:34.202998+00:00
-- url     : https://prove2.me/theorems/6362f09e-bc07-495d-87f8-549f4cd6fa2d
-- title:
--   Finite-coordinate reversal preserves total increment sum
-- statement:
--   For every finite-dimensional real vector indexed by Fin n, the sum of its coordinates is unchanged when the coordinates are reversed via Fin.rev. This holds even for n=0. The lemma is the exact algebraic invariant that the Esscher exponential density of a finite-mesh Lévy increment vector depends only on total path displacement, which is unchanged by reversal.
-- source:
--   Pinned Mathlib Fin.revPerm and Equiv.Perm.sum_comp (finite sum under permutation).

import Mathlib

open Finset
open scoped BigOperators

/-- Reversing all n finite coordinates does not change their total. -/

theorem AvramDividend.Classical.avram_ws01e_b_fin_reverse_preserves_sum (n : ℕ) (v : Fin n → ℝ) :
    (∑ i : Fin n, v i.rev) = ∑ i : Fin n, v i := by sorry
