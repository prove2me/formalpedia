-- Prove2me | Theorems.Thm_ConvexSDDP_Det_eq_10
-- name    : ConvexSDDP.Det.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:30.416329+00:00
-- url     : https://prove2.me/theorems/daf02175-dcc4-4758-a02c-0c37331fe816
-- title:
--   (10), §2, p. 7 — the new cut is tight at the visited state: $V^k_t(x^k_t)=\theta^k_t=W^{k-1}_t(x^k_t,u^k_t)$
-- statement:
--   Consider a run of the cutting-plane method (3)–(6) for the deterministic problem (1), with $x_0\in\mathcal X_0$. For every iteration $k\ge1$ and every stage $t=0,\dots,T-1$,
--   $$V^k_t(x^k_t)=\max\big(V^{k-1}_t(x^k_t),\theta^k_t\big)=\theta^k_t=W^{k-1}_t(x^k_t,u^k_t).$$
--
--   The identity says that the cut added at iteration $k$ is tight at the state where it was computed; it is how the proof of Theorem 2.1 converts statements about $\theta^k_t$ into statements about the approximations $V^k_t$.
--
--   **Formalization Note** In Lean, iteration $k+1$ gives `approx (k+1) t (x (k+1) t) = θ (k+1) t` and `θ (k+1) t = Wapprox k t (x (k+1) t) (u (k+1) t)`. The statement assumes only $x_0\in\mathcal X_0$ and the run, not (H₁): the argument on pp. 6–7 uses only the monotonicity of the approximations and the multiplier inequality (12), which applies because every visited state lies in $\mathcal X_t\subseteq\operatorname{Aff}(\mathcal X_t)$.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 7, (10) (derived on pp. 6–7 from (6), (9) and (12))

import Mathlib
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Det_Model
open Filter Topology

namespace ConvexSDDP.Det

theorem eq_10 {d p : ℕ} (M : Model d p) (hx0 : M.x0 ∈ M.X 0)
    (x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → ℕ → EuclideanSpace ℝ (Fin p))
    (θ : ℕ → ℕ → EReal) (β : ℕ → ℕ → EuclideanSpace ℝ (Fin d))
    (hrun : M.IsRun x u θ β) :
    ∀ k, ∀ t < M.T,
      M.approx θ β x (k + 1) t (x (k + 1) t) = θ (k + 1) t ∧
        θ (k + 1) t = M.Wapprox θ β x k t (x (k + 1) t) (u (k + 1) t) := by sorry

end ConvexSDDP.Det
