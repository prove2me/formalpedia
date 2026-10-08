-- Prove2me | Theorems.Thm_AdWordsMSVV_LowerBound_theorem_9
-- name    : AdWordsMSVV.LowerBound.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:56.585975+00:00
-- url     : https://prove2.me/theorems/4b48fcad-0d43-44c5-8b3f-50295a79a0eb
-- title:
--   Theorem 9, p. 15 — no randomized online algorithm for b-matching has competitive ratio better than 1 − 1/e, uniformly in the budget b
-- statement:
--   Consider online b-matching: $N$ bidders, each with the same integer budget $B \ge 1$, bidding $0$ or $1$ on each of $NB$ queries that arrive online.
--
--   For every $\delta > 0$ there is $N_0$ such that for every $N \ge N_0$, every budget $B \ge 1$ and every randomized online algorithm $A$ for instances with $N$ bidders and $NB$ queries, there exist an instance $I$ and an offline allocation $\tau$ with
--   $$\mathrm{rev}_B(I,\tau) = NB \qquad\text{and}\qquad \mathbb E_A[\mathrm{ALG}(I)] \le \Big(1-\frac1e+\delta\Big)NB.$$
--
--   Thus no randomized online algorithm achieves a competitive ratio better than $1-1/e$ for b-matching, and this holds for every budget $b$, in particular for large $b$, where the deterministic algorithm BALANCE attains $1-1/e$ in the limit. The case $B=1$ is the online bipartite matching lower bound of Karp, Vazirani and Vazirani.
--
--   **Formalization Note** "Competitive ratio better than $1-1/e$" is negated as: for every $\delta>0$ some instance has expected revenue at most $(1-1/e+\delta)$ times its optimum; the optimum is witnessed by $\tau$ (no allocation can exceed $NB$, since each of the $N$ bidders is capped at $B$). The algorithm $A$ is quantified before the instance. "For large $b$" is rendered by quantifying over every $B\ge1$ with a threshold $N_0$ independent of $B$, which implies the statement for all large $b$. The paper's instance with budget $1$ and bids $\epsilon$ is the same instance scaled by $B=1/\epsilon$.
-- source:
--   Mehta, Saberi, Vazirani, Vazirani, AdWords and generalized on-line matching, J. ACM (2007), DOI 10.1145/1284320.1284321, p. 15, Theorem 9

import Mathlib
import Definitions.Def_AdWordsMSVV_LowerBound_Setting

namespace AdWordsMSVV.LowerBound

theorem theorem_9 :
    ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ B : ℕ, 1 ≤ B →
      ∀ A : RandAlg N (N * B), ∃ (I : Instance N (N * B)) (τ : Fin (N * B) → Option (Fin N)),
        offlineRevenue B I τ = N * B ∧
        expectedRevenue B I A ≤ (1 - Real.exp (-1) + δ) * ((N : ℝ) * B) := by sorry

end AdWordsMSVV.LowerBound
