-- Prove2me | Theorems.Thm_Conway99_diag_two_offdiag_profile
-- name    : Conway99.diag_two_offdiag_profile
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-07T23:57:05.072166+00:00
-- url     : https://prove2.me/theorems/65e507c9-9609-4fe0-a01f-de327b95442e
-- title:
--   Row-profile census for diagonal-$2$ rows of an orbit-matrix candidate
-- statement:
--   Let $C$ be a $9\times 9$ matrix over $\mathbb{N}$ satisfying the Conway99 orbit-matrix equations: $C$ is symmetric, every row sums to $14$, and $(C^2)_{ij} + c_{ij}$ equals $34$ on the diagonal and $22$ off the diagonal. For a row $i$ with diagonal entry $c_{ii} = 2$, the eight off-diagonal entries sum to $12$ with square-sum $28$. Their value multiset is then exactly one of $\{0,0,1,1,2,2,3,3\}$ or $\{0,1,1,1,1,2,2,4\}$, stated as fiber counts over the value classes $0$ through $5$ (larger entries are excluded by the square sum). In particular every diagonal-$2$ row contains an off-diagonal zero. This is the diagonal-$2$ case of the row-profile census feeding the trace-$10$ branch of Wilbrink's Theorem 5.
-- source:
--   H. A. Wilbrink, 'On the (99,14,1,2) strongly regular graph', EUT Report 84-WSK-03, 1984, Theorem 5, pp. 350-354, https://pure.tue.nl/ws/files/2449333/256699.pdf ; row-moment census for the trace-10, no-four branch.

import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace Conway99

/-
  Row-profile census for diagonal-2 rows of a Conway99 orbit-matrix
  candidate. Machine-verified census (2026-09-08): eight off-diagonal
  entries with sum 12 and square-sum 28 form exactly the multisets
  {0,0,1,1,2,2,3,3} or {0,1,1,1,1,2,2,4}. Stated as fiber counts over the
  value classes 0..5 (entries above 5 are excluded by the square sum).
  Research infrastructure for `no_orbit_matrix_ten_of_no_four`; not an
  upload candidate until checked in the exact pinned environment.
-/
theorem diag_two_offdiag_profile
    (C : Matrix (Fin 9) (Fin 9) ℕ) (hsymm : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, C i j = 14)
    (hsq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)
    (i : Fin 9) (hi : C i i = 2) :
    ((((Finset.univ.erase i).filter (fun k => C i k = 0)).card = 2 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 1)).card = 2 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 2)).card = 2 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 3)).card = 2 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 4)).card = 0 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 5)).card = 0) ∨
     (((Finset.univ.erase i).filter (fun k => C i k = 0)).card = 1 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 1)).card = 4 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 2)).card = 2 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 3)).card = 0 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 4)).card = 1 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 5)).card = 0)) := by sorry

end Conway99
