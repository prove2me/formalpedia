-- Prove2me | Theorems.Thm_EDPHardness_IntegralityGap_lemma_7
-- name    : EDPHardness.IntegralityGap.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:55.804986+00:00
-- url     : https://prove2.me/theorems/77631eef-59f8-40d8-b204-6318b0b646c7
-- title:
--   Lemma 7 — Pr[ℰ₂] ≤ 1/4: at most n/β₁ vertices lie in more than 10β₂c hyperedges
-- statement:
--   Let $H$ be the random hypergraph on $n$ vertices with $\lfloor\beta_2n\rfloor$ independent hyperedges, each uniform among the $c$-subsets, with $\beta_1,\beta_2$ as in the definitions ($\log$ to base $2$, $\ln$ natural). A vertex is **high-degree** if it lies in more than $10\beta_2c$ hyperedges, and $\mathcal E_2$ is the event that more than $n/\beta_1$ vertices are high-degree.
--
--   There are absolute constants $\alpha>0$ and $N_0$ such that for every $n\ge N_0$ and every integer $c$ with $2\le c\le \alpha\,\frac{\log\log n}{\log\log\log n}$,
--   $$\Pr[\mathcal E_2]\le\frac14 .$$
--
--   Together with Lemma 6 this controls the vertices whose canonical paths are long, which the analysis of short non-canonical paths has to discard.
--
--   **Formalization Note** "Sufficiently large $n$" and the range $c\le O(\log\log n/\log\log\log n)$ are the constants $N_0$ and $\alpha$, chosen before $n$ and $c$. The probability is a normalized count over all hyperedge tuples.
-- source:
--   Andrews, Chuzhoy, Guruswami, Khanna, Talwar, Zhang, Inapproximability of Edge-Disjoint Paths and Low Congestion Routing on Undirected Graphs, Combinatorica 30 (2010), p. 493, Lemma 7

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance

namespace EDPHardness.IntegralityGap

theorem lemma_7 :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ c : ℕ, 2 ≤ c →
      (c : ℝ) ≤ α * Real.logb 2 (Real.logb 2 n) / Real.logb 2 (Real.logb 2 (Real.logb 2 n)) →
      hypProb n (numEdges n c) c (E2 n c) ≤ 1 / 4 := by sorry

end EDPHardness.IntegralityGap
