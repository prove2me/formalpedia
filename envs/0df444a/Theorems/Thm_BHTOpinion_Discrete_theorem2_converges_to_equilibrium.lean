-- Prove2me | Theorems.Thm_BHTOpinion_Discrete_theorem2_converges_to_equilibrium
-- name    : BHTOpinion.Discrete.theorem2_converges_to_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:52.6533+00:00
-- url     : https://prove2.me/theorems/9bbdbc1d-c6a6-4300-9d3c-771318e31069
-- title:
--   Theorem 2 — every proper solution of (2.1) converges to a limit x* ∈ F (distinct clusters at distance ≥ 1)
-- statement:
--   Let $x$ be a proper solution of the integral equation (2.1) for $n$ agents, where each opinion is attracted by every opinion that differs from it by less than $1$. Then $x(t)$ converges, as $t\to\infty$, to a limit $x^*\in\mathbb R^n$ that belongs to the set $F$ of equilibria:
--
--   $$\lim_{t\to\infty}x(t)=x^*,\qquad\text{and for all } i,j:\quad x^*_i\ne x^*_j\ \Longrightarrow\ |x^*_i-x^*_j|\ge 1 .$$
--
--   The opinions therefore end in clusters, all agents of a cluster sharing a common value, and distinct clusters are at least $1$ apart. This is the paper's convergence theorem for discrete agents; its continuum counterpart (Theorems 5 and 6) gives the sharper intercluster bound.
--
--   **Formalization Note** Convergence is in $\mathbb R^n$ (equivalently, of every coordinate) as real time $t\to\infty$. The theorem is stated for every proper solution: no sortedness, differentiability or eventual constancy is assumed beyond conditions (a)–(c) of the definition.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, SIAM J. Control Optim. 48 (2010), Theorem 2, p. 5219

import Mathlib
import Definitions.Def_BHTOpinion_Discrete_Model

open Filter Topology

namespace BHTOpinion.Discrete

theorem theorem2_converges_to_equilibrium {n : ℕ} (x : ℝ → Fin n → ℝ)
    (hx : IsProperSolution x) :
    ∃ xstar ∈ F n, Tendsto x atTop (𝓝 xstar) := by sorry

end BHTOpinion.Discrete
