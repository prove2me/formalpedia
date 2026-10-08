-- Prove2me | Theorems.Thm_EDPHardness_IntegralityGap_lemma_6
-- name    : EDPHardness.IntegralityGap.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:36.638713+00:00
-- url     : https://prove2.me/theorems/f19960f1-029e-452e-9996-c4073aba59b3
-- title:
--   Lemma 6 — Pr[ℰ₁] ≤ 1/4: with probability ≥ 3/4 every set of n/β₁ vertices contains a hyperedge
-- statement:
--   Let $H$ be the random hypergraph on $n$ vertices with $\lfloor\beta_2n\rfloor$ independent hyperedges, each uniform among the $c$-subsets, where $\beta_1=\frac14\big(\frac{\log n}{150(\log\log n)^2}\big)^{1/c}$, $\beta_2=6(2\beta_1)^{c-1}\ln\beta_1$ ($\log$ to base $2$, $\ln$ natural). A set of $\lceil n/\beta_1\rceil$ vertices is **bad** if it contains none of the hyperedges, and $\mathcal E_1$ is the event that a bad set exists.
--
--   There are absolute constants $\alpha>0$ and $N_0$ such that for every $n\ge N_0$ and every integer $c$ with $2\le c\le \alpha\,\frac{\log\log n}{\log\log\log n}$,
--   $$\Pr[\mathcal E_1]\le\frac14 .$$
--
--   This is the property that makes canonical routings expensive: if no bad set exists, any $\lceil n/\beta_1\rceil$ pairs routed on their canonical paths include all $c$ members of some hyperedge, which then share its special edge.
--
--   **Formalization Note** The paper states the lemma for "sufficiently large $n$" in the regime $c\le O(\log\log n/\log\log\log n)$ of Theorem 5; these two asymptotic qualifiers are the constants $N_0$ and $\alpha$, chosen before $n$ and $c$. The probability is the fraction of all $\lfloor\beta_2n\rfloor$-tuples of $c$-subsets that satisfy the event. Bad sets have size $\lceil n/\beta_1\rceil$.
-- source:
--   Andrews, Chuzhoy, Guruswami, Khanna, Talwar, Zhang, Inapproximability of Edge-Disjoint Paths and Low Congestion Routing on Undirected Graphs, Combinatorica 30 (2010), p. 492, Lemma 6 (with p. 491 for β₁, β₂ and the range of c)

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance

namespace EDPHardness.IntegralityGap

theorem lemma_6 :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ c : ℕ, 2 ≤ c →
      (c : ℝ) ≤ α * Real.logb 2 (Real.logb 2 n) / Real.logb 2 (Real.logb 2 (Real.logb 2 n)) →
      hypProb n (numEdges n c) c (E1 n c) ≤ 1 / 4 := by sorry

end EDPHardness.IntegralityGap
