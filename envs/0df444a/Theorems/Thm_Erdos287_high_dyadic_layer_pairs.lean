-- Prove2me | Theorems.Thm_Erdos287_high_dyadic_layer_pairs
-- name    : Erdos287.high_dyadic_layer_pairs
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T11:24:25.851119+00:00
-- url     : https://prove2.me/theorems/f3d93e8e-0704-40f4-a8e5-10c0ab254a69
-- title:
--   Exact pairs for high dyadic layers in dense representations
-- statement:
--   Suppose $D\subseteq[m,M]$ consists of positive denominators with reciprocal sum one and $M<3m$. If $q=2^e$ with $e\ge1$ and $M<10q$, the selected $q$-multiples are empty or exactly $\{a q,b q\}$ with $a<b$ in $\{3,5,7,9\}$ and $(a,b)\ne(3,9)$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.high_dyadic_layer_pairs (D : Finset ℕ) (m M e : ℕ) (hm : 0 < m) (he : 1 ≤ e)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hratio : M < 3 * m) (hupper : M < 10 * 2 ^ e) :
    let q := 2 ^ e
    let H := D.filter (fun n => q ∣ n)
    H = ∅ ∨ ∃ a ∈ ({3, 5, 7, 9} : Finset ℕ), ∃ b ∈ ({3, 5, 7, 9} : Finset ℕ),
      a < b ∧ (a ≠ 3 ∨ b ≠ 9) ∧ H = {a * q, b * q} := by sorry
