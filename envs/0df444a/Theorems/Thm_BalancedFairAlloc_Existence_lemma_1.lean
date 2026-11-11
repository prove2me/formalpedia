-- Prove2me | Theorems.Thm_BalancedFairAlloc_Existence_lemma_1
-- name    : BalancedFairAlloc.Existence.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:36:48.545807+00:00
-- url     : https://prove2.me/theorems/1b6fd67d-cee3-4fb5-9f49-4b6d90da3bfd
-- title:
--   Lemma 1 — no Pareto domination in a polytope iff maximizer of a positively weighted welfare (and fPO characterization)
-- statement:
--   Let $P$ be a set of real matrices $y\in\mathbb R^{N\times M}$ cut out by finitely many linear inequalities, $P=\{y:\ \sum_{i,g}D_{jig}y_{ig}\le d_j,\ j=1,\dots,k\}$, and let $x\in P$. Write $v_i(y_i)=\sum_g y_{ig}v_{ig}$. Then no $y\in P$ Pareto dominates $x$ ($v_i(y_i)\ge v_i(x_i)$ for all $i$ with one strict) if and only if there is $\alpha\in\mathbb R^n_{>0}$ with
--
--   $$\sum_i\alpha_iv_i(y_i)\le\sum_i\alpha_iv_i(x_i)\qquad\text{for all }y\in P.$$
--
--   In particular, an integral allocation $x\in P$ (entries in $\{0,1\}$, column sums at most $1$) is fPO in $P$ if and only if it maximizes such a positively weighted welfare over $P$.
--
--   This is the starting observation of the existence proof: fPO in $P_{\mathrm{bal}}$ is reduced to weighted welfare maximization with strictly positive weights.
--
--   Differences from the source:
--   - generalization: P a polytope of fractional allocations and x ∈ P a fractional allocation → P any polyhedron {y : D y ≤ d} in ℝ^{N×M} (possibly unbounded, points not required to be fractional allocations), x any point of P; reason: the proof in Appendix A uses only the representation P = {y : Dy ≤ d}; every polytope of fractional allocations is such a set, so the statement specializes to the printed one
--   - encoding: an integral allocation A ∈ P → a matrix x ∈ P with entries in {0,1} and column sums ≤ 1 (`IsIntegralAlloc`), fPO as `IsFPOIn v P x`; reason: the paper views integral allocations in matrix form (p. 9)
-- source:
--   Cookson, Shah, Verma, Fair and Efficient Balanced Allocations for Additive Valuations, arXiv:2608.06325 (held copy sha256 23649b29…), p. 10 (PDF 12), Lemma 1 (proof: Appendix A, p. 55, PDF 57)

import Mathlib
import Definitions.Def_BalancedFairAlloc_Existence_Model

namespace BalancedFairAlloc.Existence

theorem lemma_1 (n m k : ℕ) (v : Fin n → Fin m → ℝ)
    (D : Fin k → Fin n → Fin m → ℝ) (d : Fin k → ℝ) (P : Set (Fin n → Fin m → ℝ))
    (hP : P = {y | ∀ j, ∑ i, ∑ g, D j i g * y i g ≤ d j}) :
    (∀ x ∈ P,
      (¬ ∃ y ∈ P, ParetoDominates v y x) ↔
        ∃ α : Fin n → ℝ, (∀ i, 0 < α i) ∧ MaximizesWeightedWelfare v α P x) ∧
    (∀ x ∈ P, IsIntegralAlloc x →
      (IsFPOIn v P x ↔
        ∃ α : Fin n → ℝ, (∀ i, 0 < α i) ∧ MaximizesWeightedWelfare v α P x)) := by sorry

end BalancedFairAlloc.Existence
