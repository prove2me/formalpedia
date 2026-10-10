-- Prove2me | Theorems.Thm_ConvexSDDP_Det_theorem_2_1_first_part
-- name    : ConvexSDDP.Det.theorem_2_1_first_part
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:10:01.737995+00:00
-- url     : https://prove2.me/theorems/50f663be-c095-4fd3-9e40-1357838cb1f7
-- title:
--   Proof of Theorem 2.1, pp. 9–11 — exact cuts at stage $t+1$ make the decisions at stage $t$ asymptotically optimal
-- statement:
--   Under assumptions (H₁), consider a run of the cutting-plane method and a stage $t\in\{0,\dots,T-1\}$. Suppose the induction hypothesis of the proof of Theorem 2.1 holds at time $t+1$:
--   $$\lim_{k\to\infty}V_{t+1}(x^k_{t+1})-V^k_{t+1}(x^k_{t+1})=0.$$
--   Then
--   $$\lim_{k\to\infty}W_t(x^k_t,u^k_t)-V_t(x^k_t)=0,$$
--   i.e. the decisions $u^k_t$ become optimal for the true Bellman function $V_{t+1}$.
--
--   This is the first part of Theorem 2.1 at time $t$; together with the second part it carries the backward induction of the proof.
--
--   **Formalization Note** States live in $\mathbb R^d$ (`EuclideanSpace ℝ (Fin d)`) and controls in $\mathbb R^p$; values are in $\overline{\mathbb R}$ (`EReal`). The model satisfies `Model.H1`, i.e. (H₁)(1)–(6) of p. 4 together with three standing assumptions the section's proofs use but (H₁) does not list: $T>0$ ("Let $T$ be a positive integer"), every $\mathcal X_t$ ($t\le T$) is convex and compact (used on pp. 5, 8, 11), and $x_0\in\mathcal X_0$ ((1c)–(1d)). The run is the predicate `Model.IsRun`: any minimizer $u^k_t$, any multiplier $\beta^k_t$; the paper's iteration $k\ge 1$ is Lean's `k + 1`, and the approximation `approx k` is $V^k$. Limits are taken in $\overline{\mathbb R}$ (`EReal`), where $+\infty-(+\infty)=-\infty$ and $a-(-\infty)=+\infty$; convergence to $0$ therefore forces the differences to be finite for all large $k$.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, pp. 9–11, proof of Theorem 2.1 (first part at time t)

import Mathlib
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Det_Model
open Filter Topology

namespace ConvexSDDP.Det

theorem theorem_2_1_first_part {d p : ℕ} (M : Model d p) (hH1 : M.H1)
    (x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → ℕ → EuclideanSpace ℝ (Fin p))
    (θ : ℕ → ℕ → EReal) (β : ℕ → ℕ → EuclideanSpace ℝ (Fin d))
    (hrun : M.IsRun x u θ β)
    (t : ℕ) (ht : t < M.T)
    (hind : Tendsto (fun k => M.V (t + 1) (x k (t + 1)) - M.approx θ β x k (t + 1) (x k (t + 1)))
      atTop (𝓝 0)) :
    Tendsto (fun k => M.W t (x k t) (u k t) - M.V t (x k t)) atTop (𝓝 0) := by sorry

end ConvexSDDP.Det
