-- Prove2me | Theorems.Thm_CycleLengthsExp_BetaGraph_theorem_3
-- name    : CycleLengthsExp.BetaGraph.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:24:17.315333+00:00
-- url     : https://prove2.me/theorems/30b84a7e-2cf4-4102-b611-5efc84e3e945
-- title:
--   Theorem 3 — for 0 < β < 1/20 every β-graph on n vertices has a cycle of every length in [b₁ log n, (1−b₂)n], b₁ = O(1/log(1/β)), b₂ = O(β)
-- statement:
--   For every $0<\beta<\frac1{20}$ there exist positive constants $b_1=O\bigl(\frac{1}{\log(1/\beta)}\bigr)$ and $b_2=O(\beta)$ such that every β-graph $G$ on $n$ vertices contains a cycle of length $\ell$ for every integer
--   $$\ell\in\bigl[\,b_1\log n,\ (1-b_2)\,n\,\bigr].$$
--   Logarithms are to base $2$.
--
--   The set $L(G)$ of cycle lengths of a β-graph therefore contains a complete interval of length linear in $n$. This answers and improves a conjecture of Hefetz, Krivelevich and Szabó, who had the interval $[\frac{8\beta n\log n}{\log\log n},(1-3\beta)n]$ for $\beta=O(\log\log n/\log n)$; the paper notes that the order of dependence of $b_1$ and $b_2$ on $\beta$ is optimal.
--
--   **Formalization Note** The $O(\cdot)$ constants are encoded with one absolute constant $K>0$ chosen before $\beta$: $b_1\le K/\log_2(1/\beta)$ and $b_2\le K\beta$ for every $\beta\in(0,1/20)$. Since $\beta<1/20$, $\log_2(1/\beta)>4$, so the division is by a positive number. The statement is asserted for $n\ge n_0$, where $n_0$ depends on $\beta$ only; this threshold is a disclosed, necessary addition: as $\beta\to0$ the bound $b_1\to0$, and without a threshold the interval would contain $\ell=2$ at $n=3$, a length no cycle has. Graphs are on the vertex set $\{0,\dots,n-1\}$; cycles are Mathlib's `Walk.IsCycle`.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 3, Theorem 3 (restated p. 15)

import Mathlib
import Definitions.Def_CycleLengthsExp_BetaGraph_Setting

namespace CycleLengthsExp.BetaGraph

/-- Theorem 3 (p. 3, restated p. 15). For every `0 < β < 1/20` there are positive constants
`b₁ = O(1/log(1/β))` and `b₂ = O(β)` such that every β-graph `G` on `n` vertices contains a
cycle of length `ℓ` for every integer `ℓ ∈ [b₁ log n, (1 - b₂)n]`. The O-constants are one
absolute `K` fixed before `β`; `n ≥ n₀(β)` is a disclosed, necessary addition. -/
theorem theorem_3 :
    ∃ K : ℝ, 0 < K ∧ ∀ β : ℝ, 0 < β → β < 1 / 20 →
      ∃ b₁ b₂ : ℝ, 0 < b₁ ∧ b₁ ≤ K / Real.logb 2 (1 / β) ∧ 0 < b₂ ∧ b₂ ≤ K * β ∧
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ G : SimpleGraph (Fin n), IsBetaGraph β G →
          ∀ ℓ : ℕ, b₁ * Real.logb 2 n ≤ ℓ → (ℓ : ℝ) ≤ (1 - b₂) * n →
            ℓ ∈ CycleLengthsExp.WellSpread.cycleLengths G := by sorry

end CycleLengthsExp.BetaGraph
