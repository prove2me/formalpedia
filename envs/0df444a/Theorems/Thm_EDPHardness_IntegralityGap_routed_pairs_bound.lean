-- Prove2me | Theorems.Thm_EDPHardness_IntegralityGap_routed_pairs_bound
-- name    : EDPHardness.IntegralityGap.routed_pairs_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:16.947349+00:00
-- url     : https://prove2.me/theorems/5791ebf3-fee0-4676-919f-50260889f757
-- title:
--   §2.4 — |𝒫′| ≤ 4n/β₁: if none of ℰ₁, ℰ₂, ℰ₃(2g) occurs, every congestion-(c−1) routing routes ≤ 4n/β₁ pairs
-- statement:
--   Let $g=\lceil3\beta_1\beta_2c^2\rceil$. There are absolute constants $\alpha>0$ and $N_0$ such that for every $n\ge N_0$, every integer $c$ with $2\le c\le\alpha\,\frac{\log\log n}{\log\log\log n}$, and every hypergraph $H$ on $n$ vertices with $\lfloor\beta_2n\rfloor$ hyperedges of size $c$ for which none of $\mathcal E_1$, $\mathcal E_2$, $\mathcal E_3(2g)$ occurs, every integral routing in $G(H)$ with congestion at most $c-1$ routes at most
--   $$|\mathcal P'|\le\frac{4n}{\beta_1}$$
--   pairs ($\log$ to base $2$ in $\beta_1$ and in the range of $c$).
--
--   This combines the three bounds on $|\mathcal P_1|$, $|\mathcal P_2|$, $|\mathcal P_3|$ with the estimate $2gc(6\beta_2c^2)^{2g+2}\le n/\beta_1$, valid for large $n$ in this range of $c$.
--
--   **Formalization Note** "Sufficiently large $n$" and the range of $c$ are the constants $N_0$ and $\alpha$, chosen before $n$, $c$ and $H$. The page writes the final estimate as a chain $2gc(6\beta_2c^2)^{2g+2}\le(\beta_2c^2)^{3g}\le2^{4g\log\beta_2}=2^{72(4\beta_1)^c\ln^2\beta_1}\le\sqrt n\le n/\beta_1$ whose "$=$" is not an identity; only the conclusion is stated.
-- source:
--   Andrews, Chuzhoy, Guruswami, Khanna, Talwar, Zhang, Inapproximability of Edge-Disjoint Paths and Low Congestion Routing on Undirected Graphs, Combinatorica 30 (2010), p. 496, Section 2.4 (the chain for |P′3| and "In total, |P′| ⩽ 4n/β1")

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_FlowRelaxation
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance

namespace EDPHardness.IntegralityGap

theorem routed_pairs_bound :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ c : ℕ, 2 ≤ c →
      (c : ℝ) ≤ α * Real.logb 2 (Real.logb 2 n) / Real.logb 2 (Real.logb 2 (Real.logb 2 n)) →
      ∀ H : Hyp n (numEdges n c) c, ¬ E1 n c H → ¬ E2 n c H → ¬ E3 n c (2 * gParam n c) H →
      ∀ R : IntRouting (gapGraph H) (src n (numEdges n c)) (snk n (numEdges n c)) (c - 1),
        (R.routed.card : ℝ) ≤ 4 * (n : ℝ) / beta1 n c := by sorry

end EDPHardness.IntegralityGap
