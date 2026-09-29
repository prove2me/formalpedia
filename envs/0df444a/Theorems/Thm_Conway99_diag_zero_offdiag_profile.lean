-- Prove2me | Theorems.Thm_Conway99_diag_zero_offdiag_profile
-- name    : Conway99.diag_zero_offdiag_profile
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-08T00:06:54.503388+00:00
-- url     : https://prove2.me/theorems/39a8c23e-f939-42f4-97fe-34ec34d28bb3
-- title:
--   Row-profile census for diagonal-$0$ rows of an orbit-matrix candidate
-- statement:
--   Let $C$ be a $9\times 9$ matrix over $\mathbb{N}$ satisfying the Conway99 orbit-matrix equations: $C$ is symmetric, every row sums to $14$, and $(C^2)_{ij} + c_{ij}$ equals $34$ on the diagonal and $22$ off the diagonal. For a row $i$ with diagonal entry $c_{ii} = 0$, the eight off-diagonal entries sum to $14$ with square-sum $34$. Their value multiset is then exactly one of $\{0,0,2,2,2,2,3,3\}$, $\{0,1,1,1,2,3,3,3\}$, $\{0,1,1,2,2,2,2,4\}$, or $\{1,1,1,1,1,2,3,4\}$, stated as fiber counts over the value classes $0$ through $5$ (larger entries are excluded by the square sum). This is the diagonal-$0$ case of the row-profile census feeding the trace-$10$ branch of Wilbrink's Theorem 5.
-- source:
--   H. A. Wilbrink, 'On the (99,14,1,2) strongly regular graph', EUT Report 84-WSK-03, 1984, Theorem 5, pp. 350-354, https://pure.tue.nl/ws/files/2449333/256699.pdf ; row-moment census for the trace-10, no-four branch.

import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace Conway99

theorem diag_zero_offdiag_profile
    (C : Matrix (Fin 9) (Fin 9) ℕ) (hsymm : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, C i j = 14)
    (hsq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)
    (i : Fin 9) (hi : C i i = 0) :
    ((((Finset.univ.erase i).filter (fun k => C i k = 0)).card = 2 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 1)).card = 0 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 2)).card = 4 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 3)).card = 2 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 4)).card = 0 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 5)).card = 0) ∨
     (((Finset.univ.erase i).filter (fun k => C i k = 0)).card = 1 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 1)).card = 3 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 2)).card = 1 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 3)).card = 3 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 4)).card = 0 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 5)).card = 0) ∨
     (((Finset.univ.erase i).filter (fun k => C i k = 0)).card = 1 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 1)).card = 2 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 2)).card = 4 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 3)).card = 0 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 4)).card = 1 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 5)).card = 0) ∨
     (((Finset.univ.erase i).filter (fun k => C i k = 0)).card = 0 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 1)).card = 5 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 2)).card = 1 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 3)).card = 1 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 4)).card = 1 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 5)).card = 0)) := by sorry

end Conway99
