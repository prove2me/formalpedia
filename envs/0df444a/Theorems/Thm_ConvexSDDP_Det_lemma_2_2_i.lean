-- Prove2me | Theorems.Thm_ConvexSDDP_Det_lemma_2_2_i
-- name    : ConvexSDDP.Det.lemma_2_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:10:05.209013+00:00
-- url     : https://prove2.me/theorems/5fe97cdf-1c36-4695-b351-b33d1f27e4de
-- title:
--   Lemma 2.2 (i), p. 7 — the value function $V_t$ is convex and Lipschitz continuous on $\mathcal X_t$
-- statement:
--   Under assumptions (H₁), for every $t=0,\dots,T-1$ the Bellman value function $V_t$ of the DP equation (2) is convex (as a function $\mathbb R^d\to\mathbb R\cup\{+\infty\}$, equal to $+\infty$ outside $\mathcal X_t$), finite on $\mathcal X_t$, and Lipschitz continuous on $\mathcal X_t$: there is $L$ with
--   $$|V_t(y)-V_t(z)|\le L\,\|y-z\|\qquad\text{for all }y,z\in\mathcal X_t.$$
--
--   This regularity of the true Bellman functions is used in the proof of Theorem 2.1 to compare $V_{t+1}$ at two visited states (p. 11).
--
--   **Formalization Note** States live in $\mathbb R^d$ (`EuclideanSpace ℝ (Fin d)`) and controls in $\mathbb R^p$; values are in $\overline{\mathbb R}$ (`EReal`). The model satisfies `Model.H1`, i.e. (H₁)(1)–(6) of p. 4 together with three standing assumptions the section's proofs use but (H₁) does not list: $T>0$ ("Let $T$ be a positive integer"), every $\mathcal X_t$ ($t\le T$) is convex and compact (used on pp. 5, 8, 11), and $x_0\in\mathcal X_0$ ((1c)–(1d)). The run is the predicate `Model.IsRun`: any minimizer $u^k_t$, any multiplier $\beta^k_t$; the paper's iteration $k\ge 1$ is Lean's `k + 1`, and the approximation `approx k` is $V^k$. Finiteness on $\mathcal X_t$ is stated explicitly, so the real-valued difference of the Lipschitz bound is the true one.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 7, Lemma 2.2 (i)

import Mathlib
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Det_Model
open Filter Topology

namespace ConvexSDDP.Det

theorem lemma_2_2_i {d p : ℕ} (M : Model d p) (hH1 : M.H1) :
    ∀ t < M.T, EConvex (M.V t) ∧ (∀ y ∈ M.X t, M.V t y ≠ ⊤ ∧ M.V t y ≠ ⊥) ∧
      ∃ L : ℝ, ∀ y ∈ M.X t, ∀ z ∈ M.X t,
        |(M.V t y).toReal - (M.V t z).toReal| ≤ L * ‖y - z‖ := by sorry

end ConvexSDDP.Det
