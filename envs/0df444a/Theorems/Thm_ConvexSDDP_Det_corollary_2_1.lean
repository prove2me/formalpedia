-- Prove2me | Theorems.Thm_ConvexSDDP_Det_corollary_2_1
-- name    : ConvexSDDP.Det.corollary_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:10:07.269221+00:00
-- url     : https://prove2.me/theorems/68b93a55-d0f0-4881-a16f-584d87e6f31f
-- title:
--   Corollary 2.1, p. 9 — the approximations $V^k_t$ are $\alpha$-Lipschitz, with one constant $\alpha$ for all $t$ and $k$
-- statement:
--   Under assumptions (H₁), for every run of the cutting-plane method there is a constant $\alpha\ge0$ such that for every stage $t=0,\dots,T-1$ and every iteration $k$: if $V^k_t$ is finite at one point, then it is finite everywhere and
--   $$|V^k_t(y)-V^k_t(z)|\le\alpha\,\|y-z\|\qquad\text{for all }y,z\in\mathbb R^d.$$
--
--   The uniform Lipschitz constant is what allows Lemma 5.2 to be applied to the sequence $(V^k_{t+1})_k$ in the proof of Theorem 2.1 (footnote 3, p. 12).
--
--   **Formalization Note** States live in $\mathbb R^d$ (`EuclideanSpace ℝ (Fin d)`) and controls in $\mathbb R^p$; values are in $\overline{\mathbb R}$ (`EReal`). The model satisfies `Model.H1`, i.e. (H₁)(1)–(6) of p. 4 together with three standing assumptions the section's proofs use but (H₁) does not list: $T>0$ ("Let $T$ be a positive integer"), every $\mathcal X_t$ ($t\le T$) is convex and compact (used on pp. 5, 8, 11), and $x_0\in\mathcal X_0$ ((1c)–(1d)). The run is the predicate `Model.IsRun`: any minimizer $u^k_t$, any multiplier $\beta^k_t$; the paper's iteration $k\ge 1$ is Lean's `k + 1`, and the approximation `approx k` is $V^k$. The page says "for all $k\in\mathbb N^*$". Since $V^0_t\equiv-\infty$, the approximations satisfy $V^k_t\equiv-\infty$ for the first $T-1-t$ iterations, and $-\infty$ is not Lipschitz; the Lean states the property wherever $V^k_t$ is finite, which is then everywhere. The constant $\alpha$ is quantified before $t$ and $k$, as on the page.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 9, Corollary 2.1

import Mathlib
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Det_Model
open Filter Topology

namespace ConvexSDDP.Det

theorem corollary_2_1 {d p : ℕ} (M : Model d p) (hH1 : M.H1)
    (x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → ℕ → EuclideanSpace ℝ (Fin p))
    (θ : ℕ → ℕ → EReal) (β : ℕ → ℕ → EuclideanSpace ℝ (Fin d))
    (hrun : M.IsRun x u θ β) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ t < M.T, ∀ k, ∀ y z,
      M.approx θ β x k t y ≠ ⊥ →
        (M.approx θ β x k t z ≠ ⊥ ∧
          |(M.approx θ β x k t y).toReal - (M.approx θ β x k t z).toReal| ≤ α * ‖y - z‖) := by sorry

end ConvexSDDP.Det
