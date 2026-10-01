-- Prove2me | Theorems.Thm_AlonMilman_Diameter_theorem_2_5
-- name    : AlonMilman.Diameter.theorem_2_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:28:03.753902+00:00
-- url     : https://prove2.me/theorems/5e172978-9de6-438a-8ef8-d96165a5bf2b
-- title:
--   Theorem 2.5 — $b \le (1-a)/(1 + (\lambda_1/d)a\rho^2)$ for sets at distance $\rho > 1$
-- statement:
--   Let $G = (V, E)$ be a connected finite simple graph on $n \ge 2$ vertices, with maximum degree $d$ and algebraic connectivity $\lambda_1 = \lambda_1(G)$. Let $A, B \subseteq V$ and let $\rho > 1$ be an integer such that every vertex of $A$ is at graph distance at least $\rho$ from every vertex of $B$. With $a = |A|/n$ and $b = |B|/n$,
--   $$
--   b \le \frac{1 - a}{1 + (\lambda_1/d)\, a \rho^2}.
--   $$
--
--   This is the one-step isoperimetric inequality: a set $A$ of relative size $a$ leaves only a small proportion of vertices at distance at least $\rho$ from it. Iterating it gives the concentration inequality of Theorem 2.6.
--
--   **Formalization Note** As in Lemma 2.1, $\rho$ is any integer lower bound for the pairwise distances, which is equivalent to the paper's exact distance since the bound weakens as $\rho$ decreases. $A$ and $B$ may be empty: then $a = 0$ (bound $1$) or $b = 0$, and the inequality holds as stated, so no nonemptiness hypothesis is needed. $d$ is Mathlib's `SimpleGraph.maxDegree`, which is at least $1$ for a connected graph with $n \ge 2$.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 78, Theorem 2.5, Eq. (2.2)

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1

namespace AlonMilman.Diameter

theorem theorem_2_5 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (A B : Finset V) (ρ : ℕ) (hρ : 1 < ρ)
    (hdist : ∀ u ∈ A, ∀ v ∈ B, ρ ≤ G.dist u v) :
    (B.card : ℝ) / Fintype.card V ≤
      (1 - (A.card : ℝ) / Fintype.card V) /
        (1 + (lambda1 G / (G.maxDegree : ℝ)) * ((A.card : ℝ) / Fintype.card V) * (ρ : ℝ) ^ 2) := by sorry

end AlonMilman.Diameter
