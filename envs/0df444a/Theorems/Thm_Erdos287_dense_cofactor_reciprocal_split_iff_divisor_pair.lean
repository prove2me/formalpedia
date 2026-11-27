-- Prove2me | Theorems.Thm_Erdos287_dense_cofactor_reciprocal_split_iff_divisor_pair
-- name    : Erdos287.dense_cofactor_reciprocal_split_iff_divisor_pair
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-27T00:44:07.18768+00:00
-- url     : https://prove2.me/theorems/b1a50683-10a0-4b85-9b87-69caca3c36fd
-- title:
--   Classify all reciprocal splits of a dense-layer endpoint
-- statement:
--   For $0<c$ and $B<3c$, a set of distinct integers in $(c,B]$ has reciprocal sum $1/c$ exactly when it is the pair $\{c+d,c+c^2/d\}$ for a positive divisor $d<c$ of $c^2$ whose upper output is at most $B$.
-- source:
--   Erdős Problem 287. Complete classification of single-endpoint trims inside a dense cofactor layer.

import Mathlib

theorem Erdos287.dense_cofactor_reciprocal_split_iff_divisor_pair (A : Finset ℕ) (c B : ℕ) (hc : 0 < c) (hB : B < 3 * c)
    (hA : A ⊆ Finset.Ioc c B) :
    (∑ a ∈ A, (1 : ℚ) / a = (1 : ℚ) / c) ↔
      ∃ d, 0 < d ∧ d < c ∧ d ∣ c * c ∧ c + c * c / d ≤ B ∧
        A = {c + d, c + c * c / d} := by sorry
