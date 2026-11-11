-- Prove2me | Theorems.Thm_BalancedFairAlloc_Existence_lemma_22
-- name    : BalancedFairAlloc.Existence.lemma_22
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:36:47.757192+00:00
-- url     : https://prove2.me/theorems/46008e71-5414-4e94-a37f-4538abd61da9
-- title:
--   Lemma 22 — total unimodularity of the constraint matrices of P_eq and P_bal; every linear objective has an integral optimum
-- statement:
--   Let $n\ge1$, $r=\lfloor m/n\rfloor$. The constraint matrix of $P_{\mathrm{eq}}$ (one row per item $g$ with coefficient $1$ on every $x_{ig}$, one row per agent $i$ with coefficient $1$ on every $x_{ig}$) and the constraint matrix of $P_{\mathrm{bal}}$ (the same with each agent row appearing twice, once for $r\le\sum_gx_{ig}$ and once for $\sum_gx_{ig}\le r+1$) are totally unimodular. Consequently, for every objective $c\in\mathbb R^{N\times M}$ there is an integral complete allocation $A$ with matrix in $P_{\mathrm{bal}}$ such that
--
--   $$\sum_{i,g}c_{ig}y_{ig}\le\sum_{i,g}c_{ig}\,\mathbf 1[g\in A_i]\qquad\text{for all }y\in P_{\mathrm{bal}},$$
--
--   and likewise for $P_{\mathrm{eq}}$ when $n\mid m$.
--
--   The lemma makes the primal LP (5) attain its optimum at a balanced integral allocation, which is used throughout §3.
--
--   Differences from the source:
--   - encoding: constraint matrices of P_eq and P_bal → integer matrices `eqConstraintMatrix`, `balConstraintMatrix` (nonnegativity rows omitted, as in the proof: 'apart from nonnegativity'), the two-sided agent rows of P_bal as two identical copies; reason: Appendix B describes the matrices this way; negating a row (≥ to ≤ form) does not change total unimodularity
--   - reading: every linear objective attains its optimum over each polytope at an integral allocation → for every c there is a complete integral allocation A with allocMatrix A in the polytope maximizing ∑ c·y over it; reason: 'optimum' read as maximum; a minimum of c is the maximum of −c, and the integral points of P_bal and P_eq are exactly the complete allocations of the right sizes
--   - encoding: P_eq is introduced 'If s = 0' (p. 11) → the P_eq optimum clause assumes n ∣ m; reason: P_eq is empty when s ≠ 0, and the paper defines it only in that case
--   - encoding: an instance has agents → hypothesis 1 ≤ n; reason: with n = 0 and m > 0 both polytopes are empty, so no optimum exists; the paper's instances have n ≥ 1
-- source:
--   Cookson, Shah, Verma, Fair and Efficient Balanced Allocations for Additive Valuations, arXiv:2608.06325 (held copy sha256 23649b29…), p. 55 (PDF 57), Lemma 22 (Appendix B); stated on p. 11 (PDF 13)

import Mathlib
import Definitions.Def_BalancedFairAlloc_Existence_Model

namespace BalancedFairAlloc.Existence

theorem lemma_22 (n m : ℕ) (hn : 1 ≤ n) :
    (eqConstraintMatrix n m).IsTotallyUnimodular ∧
    (balConstraintMatrix n m).IsTotallyUnimodular ∧
    (n ∣ m → ∀ c : Fin n → Fin m → ℝ, ∃ A : Allocation n m, allocMatrix A ∈ Peq n m ∧
      ∀ y ∈ Peq n m, ∑ i, ∑ g, c i g * y i g ≤ ∑ i, ∑ g, c i g * allocMatrix A i g) ∧
    (∀ c : Fin n → Fin m → ℝ, ∃ A : Allocation n m, allocMatrix A ∈ Pbal n m ∧
      ∀ y ∈ Pbal n m, ∑ i, ∑ g, c i g * y i g ≤ ∑ i, ∑ g, c i g * allocMatrix A i g) := by sorry

end BalancedFairAlloc.Existence
