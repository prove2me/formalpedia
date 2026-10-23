-- Prove2me | Theorems.Thm_ConsiderChoose_StateSpace_theorem_1
-- name    : ConsiderChoose.StateSpace.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:10.79999+00:00
-- url     : https://prove2.me/theorems/2e365253-6dd8-4c5b-85fe-09163565d94e
-- title:
--   Theorem 1, p. 14 — the state space of the unique-ranking assortment DP has at most min(2^N, N·2^K) subproblems
-- statement:
--   Consider the assortment problem under a consider-then-choose model with a single preference ranking: $N$ products numbered in preference order, and $K$ customer types with consideration sets $C_1,\dots,C_K\subseteq[N]$. The dynamic program of §3 decomposes the problem along the connected components of the bipartite product–type graph, examines the products in preference order, and at each subproblem $(S,T)$ decides whether to stock $\min(S)$; each decision leaves a residual graph that splits into connected components, which become new subproblems. Let $\mathcal S$ be the set of distinct nontrivial subproblems so generated. Then
--   $$|\mathcal S|\ \le\ \min\big(2^N,\ N\cdot 2^K\big).$$
--   Moreover, for every $c\in\mathbb N$, if $K\le c\log_2 N$ then $|\mathcal S|\le N^{c+1}$.
--
--   The paper's algorithm spends $O(NK)$ operations per state, so this bound is what makes it quadratic in $N$ for a constant number of customer types and polynomial when $K=O(\log N)$, instead of examining all $2^{N+K}$ pairs $(S,T)$.
--
--   **Formalization Note.** The bound holds for every instance: the state space depends only on the consideration sets, so no hypothesis on prices or type probabilities is involved. The second sentence of the paper's Theorem 1 concerns running time, which is not formalized here (there is no operation-count model); only its state-space content is stated, as the second conjunct with $\log_2$ the floor logarithm `Nat.log 2`. States are nontrivial components (at least one product and one type); products are `Fin N` with the paper's product $1$ as `0`.
-- source:
--   Aouad, Farias & Levi (2021), Management Science 67(6), accepted manuscript (LBS eprint 1426), p. 14, Theorem 1

import Mathlib
import Definitions.Def_ConsiderChoose_StateSpace_Model

namespace ConsiderChoose.StateSpace

theorem theorem_1 {N K : ℕ} (C : Fin K → Finset (Fin N)) :
    (stateSpace C).ncard ≤ min (2 ^ N) (N * 2 ^ K) ∧
      ∀ c : ℕ, K ≤ c * Nat.log 2 N → (stateSpace C).ncard ≤ N ^ (c + 1) := by sorry

end ConsiderChoose.StateSpace
