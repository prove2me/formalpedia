-- Prove2me | Theorems.Thm_Conway99_no_four_all_entries_le_four
-- name    : Conway99.no_four_all_entries_le_four
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-08T00:53:46.699456+00:00
-- url     : https://prove2.me/theorems/7a01465a-a766-4ecd-bd5d-18727ace6d02
-- title:
--   Every entry is at most $4$ in the no-four orbit-matrix case
-- statement:
--   Let $C$ be a $9\times 9$ matrix over $\mathbb{N}$ satisfying the Conway99 orbit-matrix equations (symmetric, row sums $14$, $(C^2)_{ij}+c_{ij}$ equal to $34$ on the diagonal and $22$ off it), with every diagonal entry in $\{0,2,4\}$ and no diagonal entry equal to $4$. Then every entry of $C$ is at most $4$. Indeed each row has diagonal $0$ or $2$, and the row-profile census gives fiber counts with no $5$s in every case, while a direct square-sum argument excludes entries above $5$. This makes the entry domains finite and explicit for the trace-$10$, no-four branch of Wilbrink's Theorem 5.
-- source:
--   H. A. Wilbrink, 'On the (99,14,1,2) strongly regular graph', EUT Report 84-WSK-03, 1984, Theorem 5, pp. 350-354, https://pure.tue.nl/ws/files/2449333/256699.pdf ; entry bound for the trace-10, no-four branch.

import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace Conway99

theorem no_four_all_entries_le_four
    (C : Matrix (Fin 9) (Fin 9) ℕ) (hsymm : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, C i j = 14)
    (hsq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)
    (hdiag : ∀ i, C i i = 0 ∨ C i i = 2 ∨ C i i = 4)
    (hfour : ∀ i, C i i ≠ 4) :
    ∀ i j, C i j ≤ 4 := by sorry

end Conway99
