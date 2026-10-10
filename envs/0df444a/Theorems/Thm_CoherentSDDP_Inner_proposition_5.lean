-- Prove2me | Theorems.Thm_CoherentSDDP_Inner_proposition_5
-- name    : CoherentSDDP.Inner.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:12:17.022864+00:00
-- url     : https://prove2.me/theorems/b46ab824-9cde-4da9-a16f-22d2345ce84f
-- title:
--   Proposition 5, p. 16 — the nested risk-adjusted cost v(π̂) of the inner-approximation policy is at most y
-- statement:
--   Consider a $T$-stage stochastic linear program with stagewise independent finite outcomes,
--   $$
--   Q_t(x_{t-1},\omega_t)=\min\Big\{c_t^\top x_t+\rho_{t+1}\big(Q_{t+1}(x_t,\omega_{t+1})\big):\ A_tx_t=b_t(\omega_t)-E_tx_{t-1},\ x_t\ge0\Big\},
--   $$
--   where $T\ge2$ and each one-step risk measure $\rho_t$, $t=2,\dots,T$, is coherent (subadditive, monotone, positively homogeneous and translation equivariant). For $s=2,\dots,T$ let $x^1_{s-1},\dots,x^{J_{s-1}}_{s-1}$ be points with numbers $q^j_s$, and let $\hat{\mathcal Q}_s$ be the inner approximation they define (the lower boundary of the convex hull of the $(x^j_{s-1},q^j_s)$), with $\hat{\mathcal Q}_{T+1}\equiv0$. Assume the $q^j_s$ are upper bounds:
--   $$
--   q^j_s\ \ge\ \bar\rho_s\big(q_s(x^j_{s-1},\omega_s)\big),\qquad q_s(x_{s-1},\omega_s)=\min_{x_s\in\mathcal X_s(\omega_s)}c_s^\top x_s+\hat{\mathcal Q}_{s+1}(x_s).
--   $$
--   Let $\hat\pi$ be a policy defined by these Bellman functions: at every state and outcome with a feasible stage problem its action $\hat x_t(x_{t-1},\omega_t)$ minimizes $c_t^\top x_t+\hat{\mathcal Q}_{t+1}(x_t)$ over $\mathcal X_t(\omega_t)$, and $\hat x_1$ solves
--   $$
--   y=\min\Big\{c_1^\top x_1+\hat{\mathcal Q}_2(x_1):\ A_1x_1=b_1\Big\}. \tag{8}
--   $$
--   Let $v(\hat\pi)=c_1^\top\hat x_1+\bar\rho_2\big(\hat v_2(\hat x_1,\omega_2)\big)$ be the nested risk-adjusted cost of $\hat\pi$, where $\hat v_t(x_{t-1},\omega_t)=c_t^\top\hat x_t+\bar\rho_{t+1}(\hat v_{t+1}(\hat x_t,\omega_{t+1}))$ is the actual risk-adjusted cost of $\hat\pi$ over stages $t,\dots,T$. Then
--   $$
--   v(\hat\pi)\ \le\ y .
--   $$
--
--   Thus the optimal value $y$ of the first-stage problem built on the inner approximation is a deterministic upper bound on the risk-adjusted cost of the policy it defines; together with the lower bound from outer approximation it brackets the cost of a computable risk-averse policy, which is otherwise hard to estimate by sampling under a nested risk measure.
--
--   **Formalization Note** Costs live in $\mathbb R\cup\{+\infty\}$ (`EReal`); $\bar\rho_t$ is $+\infty$ when some outcome has infinite cost, an infeasible stage costs $+\infty$, and $\hat{\mathcal Q}_s$ is $+\infty$ off the convex hull of its points. The bound is trivially true when $y=+\infty$; it is informative when $\hat x_1$ lies in the convex hull of the stage-1 points. Standing assumptions made explicit: $T\ge2$; $\rho_t$ coherent for $t=2,\dots,T$; the terminal convention $\rho_{T+1}(Q_{T+1})=0$ (the first option on p. 4, used in the proof); (8) without $x_1\ge0$, as printed. The upper-bound hypothesis is stated for the risk-adjusted optimal value of the stage problem (13) at the points, the form the proof uses on p. 17 ("$\hat{\mathcal Q}_t(x_{t-1})$ is an inner approximation of the risk-adjusted optimal value function of (13)") and the Upper Bound Computation (U) computes on p. 18; p. 16 phrases it as a bound on the true value $\rho_{t+1}(Q_{t+1}(x_t,\omega_{t+1}))$, under which the proof does not go through. The policy is any selection with the minimizing property, required at every feasible state.
-- source:
--   Philpott, de Matos & Finardi, On Solving Multistage Stochastic Programs with Coherent Risk Measures, authors' manuscript of 13 August 2012 (Operations Research, 2013), p. 16, Proposition 5 (proof pp. 16–17); setting pp. 3–4, (1), (2); p. 9, (8); p. 18, Upper Bound Computation (U)

import Mathlib
import Definitions.Def_CoherentSDDP_Inner_Basic
import Definitions.Def_CoherentSDDP_Inner_Model

namespace CoherentSDDP.Inner

theorem proposition_5 {n m : ℕ} {Ω : ℕ → Type} [∀ t, Fintype (Ω t)] [∀ t, Nonempty (Ω t)]
    (M : Model n m Ω) (hT : 2 ≤ M.T) (hρ : ∀ t, 2 ≤ t → t ≤ M.T → IsCoherent (M.ρ t))
    (D : InnerData n) (hD : UpperBounds M D)
    (xhat : (t : ℕ) → (Fin n → ℝ) → Ω t → Fin n → ℝ) (x1hat : Fin n → ℝ)
    (hπ : IsInnerPolicy M D xhat x1hat) :
    vpi M xhat x1hat ≤ y M D := by sorry

end CoherentSDDP.Inner
