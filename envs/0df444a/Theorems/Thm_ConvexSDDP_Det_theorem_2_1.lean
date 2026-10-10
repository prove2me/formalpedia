-- Prove2me | Theorems.Thm_ConvexSDDP_Det_theorem_2_1
-- name    : ConvexSDDP.Det.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:41.651326+00:00
-- url     : https://prove2.me/theorems/65eeb1b9-958c-46d5-a6bf-fe80480e4696
-- title:
--   Theorem 2.1, p. 9 — along the generated trajectories the decisions become optimal and the cuts exact at every stage
-- statement:
--   Consider the deterministic multistage convex control problem (1) under assumptions (H₁), its Bellman functions $V_t$ (2) and $W_t(x,u)=C_t(x,u)+V_{t+1}(f_t(x,u))$ (8). Let $(x^k_t,u^k_t,\theta^k_t,\beta^k_t)_{k\ge1}$ be any run of the cutting-plane method (3)–(6): at iteration $k$, starting from $x^k_0=x_0$, $u^k_t$ is a minimizer of the stage problem (3) with the current approximation $V^{k-1}_{t+1}$, $\theta^k_t$ its optimal value, $\beta^k_t$ a Lagrange multiplier of the state constraint, $x^k_{t+1}=f_t(x^k_t,u^k_t)$, and $V^k_t=\max(V^{k-1}_t,\theta^k_t+\langle\beta^k_t,\cdot-x^k_t\rangle)$ with $V^0_t\equiv-\infty$, $V^k_T=V_T$. Then for every $t=0,\dots,T-1$,
--   $$\lim_{k\to\infty}W_t(x^k_t,u^k_t)-V_t(x^k_t)=0\qquad\text{and}\qquad\lim_{k\to\infty}V_t(x^k_t)-V^k_t(x^k_t)=0.$$
--
--   The first limit says that the decisions computed with the approximate Bellman functions become optimal for the true ones; the second that the lower approximations become exact at the visited states. The approximations need not converge away from the generated trajectories.
--
--   **Formalization Note** States live in $\mathbb R^d$ (`EuclideanSpace ℝ (Fin d)`) and controls in $\mathbb R^p$; values are in $\overline{\mathbb R}$ (`EReal`). The model satisfies `Model.H1`, i.e. (H₁)(1)–(6) of p. 4 together with three standing assumptions the section's proofs use but (H₁) does not list: $T>0$ ("Let $T$ be a positive integer"), every $\mathcal X_t$ ($t\le T$) is convex and compact (used on pp. 5, 8, 11), and $x_0\in\mathcal X_0$ ((1c)–(1d)). The run is the predicate `Model.IsRun`: any minimizer $u^k_t$, any multiplier $\beta^k_t$; the paper's iteration $k\ge 1$ is Lean's `k + 1`, and the approximation `approx k` is $V^k$. Limits are taken in $\overline{\mathbb R}$ (`EReal`), where $+\infty-(+\infty)=-\infty$ and $a-(-\infty)=+\infty$; convergence to $0$ therefore forces both differences to be finite for all large $k$. The theorem is about every run; `run_exists` shows that runs exist for every model satisfying (H₁).
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 9, Theorem 2.1

import Mathlib
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Det_Model
open Filter Topology

namespace ConvexSDDP.Det

theorem theorem_2_1 {d p : ℕ} (M : Model d p) (hH1 : M.H1)
    (x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → ℕ → EuclideanSpace ℝ (Fin p))
    (θ : ℕ → ℕ → EReal) (β : ℕ → ℕ → EuclideanSpace ℝ (Fin d))
    (hrun : M.IsRun x u θ β) :
    ∀ t < M.T,
      Tendsto (fun k => M.W t (x k t) (u k t) - M.V t (x k t)) atTop (𝓝 0) ∧
        Tendsto (fun k => M.V t (x k t) - M.approx θ β x k t (x k t)) atTop (𝓝 0) := by sorry

end ConvexSDDP.Det
