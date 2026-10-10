-- Prove2me | Theorems.Thm_ConvexSDDP_Det_lemma_2_2_ii
-- name    : ConvexSDDP.Det.lemma_2_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:42.359269+00:00
-- url     : https://prove2.me/theorems/dba386bd-c289-4dbe-af62-e72a75959e23
-- title:
--   Lemma 2.2 (ii), p. 7 — the cuts are valid: $V^k_t\le\tilde V_t\le V_t$
-- statement:
--   Under assumptions (H₁), for every run of the cutting-plane method, every iteration $k\ge0$ and every stage $t=0,\dots,T-1$:
--   $$V^k_t(y)\le\tilde V_t(y)\quad\text{for all }y\in\operatorname{Aff}(\mathcal X_t),\qquad \tilde V_t(y)\le V_t(y)\quad\text{for all }y\in\mathbb R^d,$$
--   where $\tilde V_t(y)=\inf_{u\in\mathcal U_t(y)}C_t(y,u)+V_{t+1}(f_t(y,u))$ is the extended value function (11). For $k=0$ this is $V^0_t\equiv-\infty$.
--
--   The inequality says that the cutting-plane approximations are lower bounds of the Bellman functions; it bounds the multipliers in (iii) and gives Corollary 2.1.
--
--   **Formalization Note** States live in $\mathbb R^d$ (`EuclideanSpace ℝ (Fin d)`) and controls in $\mathbb R^p$; values are in $\overline{\mathbb R}$ (`EReal`). The model satisfies `Model.H1`, i.e. (H₁)(1)–(6) of p. 4 together with three standing assumptions the section's proofs use but (H₁) does not list: $T>0$ ("Let $T$ be a positive integer"), every $\mathcal X_t$ ($t\le T$) is convex and compact (used on pp. 5, 8, 11), and $x_0\in\mathcal X_0$ ((1c)–(1d)). The run is the predicate `Model.IsRun`: any minimizer $u^k_t$, any multiplier $\beta^k_t$; the paper's iteration $k\ge 1$ is Lean's `k + 1`, and the approximation `approx k` is $V^k$. The page states $V^k_t\le\tilde V_t$ on all of $\mathbb R^n$. Its proof derives it from (12), which only controls the cuts on $\operatorname{Aff}(\mathcal X_t)$, and outside the affine hull the printed inequality can fail: with $d=p=1$, $T=1$, $\mathcal X_0=\mathcal X_1=\{0\}$, $\mathcal U_0\equiv\{0\}$, $C_0(x,u)=x$, $f_0=0$, $V_1=0$, the multiplier must be $\beta^1_0=0$, the cut is the constant $0$, while $\tilde V_0(y)=y<0$ for $y<0$. The Lean states the first inequality on $\operatorname{Aff}(\mathcal X_t)$, which is everything the paper uses (the points $x^k_t$ and $\mathcal X''_t$ of (16)). "$\beta^k_t$ is defined" (the existence of the multipliers) is the companion item `run_exists`.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 7, Lemma 2.2 (ii)

import Mathlib
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Det_Model
open Filter Topology

namespace ConvexSDDP.Det

theorem lemma_2_2_ii {d p : ℕ} (M : Model d p) (hH1 : M.H1)
    (x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → ℕ → EuclideanSpace ℝ (Fin p))
    (θ : ℕ → ℕ → EReal) (β : ℕ → ℕ → EuclideanSpace ℝ (Fin d))
    (hrun : M.IsRun x u θ β) :
    ∀ k, ∀ t < M.T,
      (∀ y ∈ affineSpan ℝ (M.X t), M.approx θ β x k t y ≤ M.Vtilde t y) ∧
        ∀ y, M.Vtilde t y ≤ M.V t y := by sorry

end ConvexSDDP.Det
