-- Prove2me | Theorems.Thm_ConvexSDDP_Det_theorem_2_1_second_part
-- name    : ConvexSDDP.Det.theorem_2_1_second_part
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:52.759724+00:00
-- url     : https://prove2.me/theorems/ea2a4f3b-cb10-44d1-bd6b-282de8aa2fa4
-- title:
--   Proof of Theorem 2.1, pp. 11–12 — the cuts at stage $t$ become exact along the trajectory
-- statement:
--   Under assumptions (H₁), consider a run of the cutting-plane method and a stage $t\in\{0,\dots,T-1\}$. Suppose that
--   $$\lim_{k\to\infty}V_{t+1}(x^k_{t+1})-V^k_{t+1}(x^k_{t+1})=0\qquad\text{and}\qquad\lim_{k\to\infty}W_t(x^k_t,u^k_t)-V_t(x^k_t)=0.$$
--   Then
--   $$\lim_{k\to\infty}V_t(x^k_t)-V^k_t(x^k_t)=0,$$
--   which is the induction hypothesis at time $t$ ("We now have to show the induction hypothesis, namely $\lim_{k\to+\infty}V_t(x^k_t)-V^k_t(x^k_t)=0$ for time $t$", p. 11).
--
--   This is the second part of Theorem 2.1 at time $t$; the step uses (10), Lemma 5.2 and Corollary 2.1.
--
--   **Formalization Note** States live in $\mathbb R^d$ (`EuclideanSpace ℝ (Fin d)`) and controls in $\mathbb R^p$; values are in $\overline{\mathbb R}$ (`EReal`). The model satisfies `Model.H1`, i.e. (H₁)(1)–(6) of p. 4 together with three standing assumptions the section's proofs use but (H₁) does not list: $T>0$ ("Let $T$ be a positive integer"), every $\mathcal X_t$ ($t\le T$) is convex and compact (used on pp. 5, 8, 11), and $x_0\in\mathcal X_0$ ((1c)–(1d)). The run is the predicate `Model.IsRun`: any minimizer $u^k_t$, any multiplier $\beta^k_t$; the paper's iteration $k\ge 1$ is Lean's `k + 1`, and the approximation `approx k` is $V^k$. Limits are taken in $\overline{\mathbb R}$ (`EReal`); convergence to $0$ forces the differences to be finite for all large $k$.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, pp. 11–12, proof of Theorem 2.1 (second part at time t)

import Mathlib
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Det_Model
open Filter Topology

namespace ConvexSDDP.Det

theorem theorem_2_1_second_part {d p : ℕ} (M : Model d p) (hH1 : M.H1)
    (x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → ℕ → EuclideanSpace ℝ (Fin p))
    (θ : ℕ → ℕ → EReal) (β : ℕ → ℕ → EuclideanSpace ℝ (Fin d))
    (hrun : M.IsRun x u θ β)
    (t : ℕ) (ht : t < M.T)
    (hind : Tendsto (fun k => M.V (t + 1) (x k (t + 1)) - M.approx θ β x k (t + 1) (x k (t + 1)))
      atTop (𝓝 0))
    (hfirst : Tendsto (fun k => M.W t (x k t) (u k t) - M.V t (x k t)) atTop (𝓝 0)) :
    Tendsto (fun k => M.V t (x k t) - M.approx θ β x k t (x k t)) atTop (𝓝 0) := by sorry

end ConvexSDDP.Det
