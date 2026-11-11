-- Prove2me | Theorems.Thm_BalancedFairAlloc_Existence_lemma_13
-- name    : BalancedFairAlloc.Existence.lemma_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:37:37.788903+00:00
-- url     : https://prove2.me/theorems/e60da578-32a4-43ed-bbd2-e555cd059449
-- title:
--   Lemma 13 — a balanced allocation maximizing a ρ-bounded weighted welfare over P_bal with f_ij ≤ γ
-- statement:
--   Suppose $n\ge2$, $r\ge1$ and $|v_{ig}|\le V$ for all $i,g$. Let $H=2(r+2)V$ and $K=2(r+1)V$. For every $\gamma>0$ and every $\rho$ with $0<\rho<\gamma/[2n(\gamma+H+(n-1)K)]$ there are a balanced allocation $A$ and weights $\alpha\in\Delta$ with $\alpha_i\ge\rho$ for all $i$ such that
--
--   $$A\in\arg\max_{x\in P_{\mathrm{bal}}}\sum_i\alpha_iv_i(x_i)\qquad\text{and}\qquad f_{ij}(A)\le\gamma\ \text{ for all } i,j\in N.$$
--
--   By Lemma 1, $A$ is fPO in $P_{\mathrm{bal}}$; letting $\gamma\to0$ over the finitely many balanced allocations gives Theorem 1.
--
--   Differences from the source:
--   - encoding: A ∈ argmax_{x ∈ P_bal} ∑_i α_i v_i(x_i) → `MaximizesWeightedWelfare v α (Pbal n m) (allocMatrix A)`: the matrix of A lies in P_bal and its weighted welfare is at least that of every y ∈ P_bal; reason: definition of argmax
--   - encoding: α ∈ {y ∈ Δ : y_i ≥ ρ} → α ∈ `stdSimplex ℝ (Fin n)` and ρ ≤ α i for all i; reason: same set
--   - encoding: H := 2(r+2)V, K := 2(r+1)V → real variables H, K with defining equations, r = `m / n` cast to ℝ; reason: same numbers
-- source:
--   Cookson, Shah, Verma, Fair and Efficient Balanced Allocations for Additive Valuations, arXiv:2608.06325 (held copy sha256 23649b29…), p. 25 (PDF 27), Lemma 13

import Mathlib
import Definitions.Def_BalancedFairAlloc_Existence_Model
import Definitions.Def_BalancedFairAlloc_Existence_Score

namespace BalancedFairAlloc.Existence

theorem lemma_13 (n m : ℕ) (hn : 2 ≤ n) (hr : 1 ≤ m / n) (v : Fin n → Fin m → ℝ)
    (V : ℝ) (hV : ∀ i g, |v i g| ≤ V)
    (H K : ℝ) (hH : H = 2 * (((m / n : ℕ) : ℝ) + 2) * V)
    (hK : K = 2 * (((m / n : ℕ) : ℝ) + 1) * V)
    (γ ρ : ℝ) (hγ : 0 < γ) (hρ0 : 0 < ρ)
    (hρ : ρ < γ / (2 * (n : ℝ) * (γ + H + ((n : ℝ) - 1) * K))) :
    ∃ (A : Allocation n m) (α : Fin n → ℝ),
      IsBalanced A ∧ α ∈ stdSimplex ℝ (Fin n) ∧ (∀ i, ρ ≤ α i) ∧
      MaximizesWeightedWelfare v α (Pbal n m) (allocMatrix A) ∧
      ∀ i j, residualEnvy v A i j ≤ γ := by sorry

end BalancedFairAlloc.Existence
