-- Prove2me | Theorems.Thm_DetConnSketch_Main_claim_4_8
-- name    : DetConnSketch.Main.claim_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:42:18.633533+00:00
-- url     : https://prove2.me/theorems/d4e77fa3-91c4-4214-9709-d87039eae092
-- title:
--   Claim 4.8 — at most $\min\{(3n)^{2R(t+2)},(3n)^{2k+2}\}$ sparse $\{-1,0,1\}$-matrices of rank $R$
-- statement:
--   Let $n \ge 1$, let $s = n - u \le n$, and let $\mathbb F$ be a finite field. The number of matrices $N \in \{-1,0,1\}^{s\times s}$ such that every row and every column has at most $t$ nonzero entries, there are at most $k$ nonzero entries overall, and $N$ has rank $R$ over $\mathbb F$, is at most
--   $$\min\big\{(3n)^{2R(t+2)},\ (3n)^{2k+2}\big\}.$$
--
--   It is the counting half of the union bound in the proof of Lemma 4.4, where the field is $\mathbb F_q$ with $q = 3^{\lceil 1000\log_3(3n)\rceil}$.
--
--   Differences from the source:
--   - encoding: N has rank R over F_q → F an arbitrary finite field; rank of the entrywise integer cast of N; reason: the printed claim does not assume odd characteristic; its characteristic-2 counterexample is retained separately in INSIGHTS.yaml I1
--   - reading: (n − u) × (n − u) with n the number of vertices → s ≤ n with 1 ≤ n; reason: n is the positive ambient number of vertices; s = n − u ranges over 0 ≤ s ≤ n, including an empty remainder
--   - encoding: the total number of such matrices → Nat.card of the subtype of integer matrices satisfying all conditions; reason: the set is finite since entries lie in {−1, 0, 1}
--   - encoding: row, column and total sparsity parameters t and k → t and k are natural numbers; reason: nonnegative real thresholds reduce to their floors without changing the counted set; both bounds increase with the thresholds since 3n ≥ 3
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 27 (PDF 31), Claim 4.8

import Mathlib
import Definitions.Def_DetConnSketch_Main_SketchMatrices

namespace DetConnSketch.Main

/-- Claim 4.8: over a finite field `F`, the number of matrices
`N ∈ {−1, 0, 1}^{s×s}` (`s = n − u ≤ n`) with at most `t` nonzero entries in every row and
column, at most `k` nonzero entries in total and rank `R` over `F` is at most
`min{(3n)^{2R(t+2)}, (3n)^{2k+2}}`. -/
theorem claim_4_8 (F : Type) [Field F] [Fintype F]
    (n s t k R : ℕ) (hn : 1 ≤ n) (hs : s ≤ n) :
    (Nat.card {N : Matrix (Fin s) (Fin s) ℤ //
        (∀ i j, N i j = -1 ∨ N i j = 0 ∨ N i j = 1) ∧
        (∀ i, rowNnz N i ≤ t) ∧ (∀ j, colNnz N j ≤ t) ∧ nnz N ≤ k ∧
        (N.map (Int.cast : ℤ → F)).rank = R} : ℝ) ≤
      min ((3 * (n : ℝ)) ^ (2 * R * (t + 2))) ((3 * (n : ℝ)) ^ (2 * k + 2)) := by sorry

end DetConnSketch.Main
