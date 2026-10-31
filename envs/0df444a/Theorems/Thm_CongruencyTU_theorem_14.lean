-- Prove2me | Theorems.Thm_CongruencyTU_theorem_14
-- name    : CongruencyTU.theorem_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:35.839742+00:00
-- url     : https://prove2.me/theorems/58be9a55-1caf-4419-8050-6d0957877820
-- title:
--   Theorem 14 (Seymour's TU decomposition): every TU matrix is a base block or decomposes, and the case is computable in strongly polynomial time
-- statement:
--   Let $T\in\mathbb Z^{k\times n}$ be totally unimodular. Then one of the following holds.
--
--   1. $T$ or $T^\top$ is a network matrix.
--   2. After iteratively deleting rows or columns with at most one non-zero entry, deleting rows or columns that appear twice or whose negation also appears, and changing signs of rows or columns, $T$ equals one of the two $5\times5$ matrices of case (ii).
--   3. After row and column permutations, $T$ is a 1-, 2- or 3-sum of totally unimodular matrices with $n_A,n_B\ge2$.
--   4. After pivoting once and row and column permutations, $T$ is a 3-sum of totally unimodular matrices with $n_A,n_B\ge2$.
--
--   Moreover, one can decide in polynomial time which case holds and determine the involved matrices.
--
--   This is the decomposition along which the proof of Theorem 2 recurses; the bound $n_A,n_B\ge2$ guarantees progress.
--
--   **Formalization Note** The first conjunct is the case distinction; the second is one deterministic program that outputs a case together with its data (`SeymourOut`).
--
--   Differences from the source:
--
--   - reading: "we can in time poly(n) decide which of the cases holds and determine the involved matrices" → a deterministic strongly polynomial program on [k, n] ++ T (cost polynomial in the input dimension, bit lengths polynomial in the input bit size) whose output names a case that holds with its data: the network matrix (T or T⊤), the 5 × 5 matrix, the decomposition, or the pivot entry and the decomposition of the pivoted matrix; reason: the involved matrices have up to k rows and k is not bounded in n, so they cannot be written in poly(n) time; the network structure itself is not output
--   - reading: case (ii): "equal to one of" the two matrices → equal after a bijection of the surviving rows and columns with those of the displayed matrix (and sign changes); reason: the order of the surviving rows is not meaningful; a row-swapped copy of the first matrix would otherwise fall into no case
--   - encoding: iterated deletions and sign changes → a submatrix reachable by deletions (DelReachable), then sign changes of its rows and columns; reason: both deletion rules are invariant under sign changes, so sign changes can be performed last
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, p.8 (PDF p.9), Theorem 14

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_CongruencyTU_Instance
import Definitions.Def_CongruencyTU_Seymour

namespace CongruencyTU

/-- **Theorem 14 (Seymour's TU decomposition)** (Nägele–Santiago–Zenklusen, *Congruency-Constrained TU Problems Beyond the Bimodular Case*, arXiv:2109.03148v3 (preprint), p.8, PDF p.9): "Let T ∈ ℤ^{k×n} be a totally
unimodular matrix. Then, one of the following cases holds. (i) T or T⊤ is a network matrix. (ii) T
is, possibly after iteratively applying the operations of – deleting a row or column with at most
one non-zero entry, – deleting a row or column that appears twice or whose negation also appears in
the matrix, and – changing the sign of a row or column, equal to one of [two 5 × 5 matrices].
(iii) T can, possibly after row and column permutations, be decomposed into a 1-, 2-, or 3-sum of
totally unimodular matrices with nA, nB ≥ 2. (iv) T can, after pivoting once and possibly
performing row and column permutations, be decomposed into a 3-sum of totally unimodular matrices
with nA, nB ≥ 2. Additionally, we can in time poly(n) decide which of the cases holds and determine
the involved matrices."

First conjunct: the case distinction. Second conjunct: one deterministic strongly polynomial program
that, on `[k, n] ++ entries of T` for a totally unimodular `T`, outputs a case that holds together
with its data (`SeymourOut`: which matrix is a network matrix; which `5 × 5` matrix; the
permutations and the summands of the sum; the pivot entry and the 3-sum of the pivoted matrix).

**Formalization Note.** "In time poly(n)" is read as polynomial in the input dimension (the
summands have up to `k` rows and `k` is not bounded by `n`). Case (ii) is matched up to the order
of the surviving rows and columns (see `Def_CongruencyTU_Seymour`). -/
theorem theorem_14 :
    (∀ {k n : ℕ} (T : Matrix (Fin k) (Fin n) ℤ), T.IsTotallyUnimodular →
      SeymourCase1 T ∨ SeymourCase2 T ∨ SeymourCase3 T ∨ SeymourCase4 T) ∧
    DetSolves (fun M : (k : ℕ) × (n : ℕ) × Matrix (Fin k) (Fin n) ℤ =>
        [(M.1 : ℤ), (M.2.1 : ℤ)] ++ encMat M.2.2)
      (fun M => ([(M.1 : ℤ), (M.2.1 : ℤ)] ++ encMat M.2.2).length)
      (fun M => M.2.2.IsTotallyUnimodular) (fun M out => SeymourOut M.2.2 out) := by sorry

end CongruencyTU
