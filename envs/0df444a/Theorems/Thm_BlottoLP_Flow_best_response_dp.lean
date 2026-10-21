-- Prove2me | Theorems.Thm_BlottoLP_Flow_best_response_dp
-- name    : BlottoLP.Flow.best_response_dp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:56.297414+00:00
-- url     : https://prove2.me/theorems/5e750149-3260-48eb-954b-c8630f5182de
-- title:
--   Proof of Theorem 4.6, p. 10 (corrected) — best response = maximum-weight path, certified by the DP rows of LP1-(b)
-- statement:
--   Let $W=(W_{k,i})$, $1\le k\le K$, $0\le i\le N$, be real weights, where $W_{k,i}$ is the weight of the edges $v_{k-1,j}\to v_{k,j+i}$ of the layered graph of a player with $N$ troops, so that a pure strategy $y$ (a canonical path) has weight $\sum_k W_{k,y_k}$. For every real $t$,
--   $$
--   \Big(\forall y:\ \sum_{k=1}^{K} W_{k,y_k}\le t\Big)\iff \exists D:\ D_{0,0}=0,\ \ D_{k,i}\ge D_{k-1,j}+W_{k,i-j}\ (1\le k\le K,\ 0\le j\le i\le N),\ \ D_{K,N}\le t.
--   $$
--   That is, the maximum weight of a canonical path is at most $t$ exactly when the dynamic-programming rows of Linear Program 1-(b) have a solution with $D_{K,N}\le t$.
--
--   With $W=W^B$ from eq. (4), the left side says that no pure strategy of B earns more than $t$ against A's marginals; this is how Linear Program 1 encodes the exponentially many payoff constraints with $O(N^2K)$ rows.
--
--   **Formalization Note** The printed LP1 fixes $D_{0,i}=0$ for every $0\le i\le N$. With that row the implication "$\Rightarrow$" fails, because paths may then start at $v_{0,i}$ with $i>0$ (allocations of fewer than $N$ troops). The statement uses the corrected row $D_{0,0}=0$ only, with $D_{0,i}$ free for $i>0$, and the index $W_{k,i-j}$ for the paper's $W^B_{k-1,i-j}$.
-- source:
--   Behnezhad, Dehghani, Derakhshan, Hajiaghayi, Seddighin, Faster and Simpler Algorithm for Optimal Strategies of Blotto Game, arXiv preprint (arXiv:1612.04029, PDF of 2016-12-28), p. 10, proof of Theorem 4.6 (maximum-weight path and the constraint D^B_{k,i} ≥ D^B_{k−1,j} + W^B_{k−1,i−j}), corrected

import Mathlib
import Definitions.Def_BlottoLP_Flow_Model

namespace BlottoLP.Flow

/-- Proof of Theorem 4.6, p. 10 (corrected): with weight `W k i` on the edges
`v_{k,j} → v_{k+1,j+i}` of the layered graph of a player with `N` troops, every pure strategy has
weight at most `t` (the maximum-weight canonical path weighs at most `t`) if and only if the
dynamic-programming rows of Linear Program 1-(b), with `D_{0,0} = 0`, have a solution with
`D_{K,N} ≤ t`. -/
theorem best_response_dp (K N : ℕ) (W : Fin K → Fin (N + 1) → ℝ) (t : ℝ) :
    (∀ y : Pure K N, ∑ k, W k (y.1 k) ≤ t) ↔
      ∃ D : Fin (K + 1) → Fin (N + 1) → ℝ, IsDPBound W D ∧ D (Fin.last K) (Fin.last N) ≤ t := by sorry

end BlottoLP.Flow
