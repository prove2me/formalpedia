-- Prove2me | Theorems.Thm_EDPHardness_IntegralityGap_good_event
-- name    : EDPHardness.IntegralityGap.good_event
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:57.077989+00:00
-- url     : https://prove2.me/theorems/0c57f11e-0852-498d-9dfb-ebc446bac4e1
-- title:
--   §2.4 ¶1 — with probability ≥ 1/4 none of ℰ₁, ℰ₂, ℰ₃(2g) occurs, g = 3β₁β₂c²
-- statement:
--   Let $H$ be the random hypergraph of the mission ($n$ vertices, $\lfloor\beta_2n\rfloor$ independent uniform $c$-subsets), and let $g=\lceil3\beta_1\beta_2c^2\rceil$.
--
--   There are absolute constants $\alpha>0$ and $N_0$ such that for every $n\ge N_0$ and every integer $c$ with $2\le c\le\alpha\,\frac{\log\log n}{\log\log\log n}$,
--   $$\Pr\big[\neg\mathcal E_1\wedge\neg\mathcal E_2\wedge\neg\mathcal E_3(2g)\big]\ge\frac14,$$
--   where $\mathcal E_3(2g)$ is the event that $G'$ has more than $(6\beta_2c^2)^{2g+1}$ cycles of length at most $2g$.
--
--   This is the step where the probabilistic part ends: a hypergraph with all three good properties exists, and the rest of the analysis is deterministic.
--
--   **Formalization Note** "Sufficiently large $n$" and the range of $c$ are the constants $N_0$ and $\alpha$, chosen before $n$ and $c$; $g$ is rounded up to an integer.
-- source:
--   Andrews, Chuzhoy, Guruswami, Khanna, Talwar, Zhang, Inapproximability of Edge-Disjoint Paths and Low Congestion Routing on Undirected Graphs, Combinatorica 30 (2010), p. 495, Section 2.4, first paragraph

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance

namespace EDPHardness.IntegralityGap

theorem good_event :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ c : ℕ, 2 ≤ c →
      (c : ℝ) ≤ α * Real.logb 2 (Real.logb 2 n) / Real.logb 2 (Real.logb 2 (Real.logb 2 n)) →
      1 / 4 ≤ hypProb n (numEdges n c) c
        (fun H => ¬ E1 n c H ∧ ¬ E2 n c H ∧ ¬ E3 n c (2 * gParam n c) H) := by sorry

end EDPHardness.IntegralityGap
