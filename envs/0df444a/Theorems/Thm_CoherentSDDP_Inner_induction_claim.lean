-- Prove2me | Theorems.Thm_CoherentSDDP_Inner_induction_claim
-- name    : CoherentSDDP.Inner.induction_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:13:26.151875+00:00
-- url     : https://prove2.me/theorems/e1b586a6-7c61-404e-89f1-fde734902e5a
-- title:
--   Proof of Proposition 5, p. 16 — for every x_{t−1}, ρ̄ₜ(v̂ₜ(x_{t−1}, ω_t)) ≤ 𝒬̂ₜ(x_{t−1}), t = 2, …, T
-- statement:
--   Consider the model of the paper with $T\ge2$ stages, coherent one-step risk measures $\rho_t$ for $t=2,\dots,T$, inner-approximation data whose bounds are upper bounds in the sense of the model file ($q^j_s\ge\bar\rho_s(q_s(x^j_{s-1},\omega_s))$ for $s=2,\dots,T$), and a policy $\hat\pi$ defined by the inner approximation (each $\hat x_t(x_{t-1},\omega_t)$ minimizes (13) wherever (13) is feasible, and $\hat x_1$ solves (8)). Let $\hat v_t$ be the actual risk-adjusted cost of $\hat\pi$ over stages $t,\dots,T$. Then for every $t=2,\dots,T$ and every state $x_{t-1}$,
--   $$
--   \bar\rho_t\big(\hat v_t(x_{t-1},\omega_t)\big)\ \le\ \hat{\mathcal Q}_t(x_{t-1}).
--   $$
--
--   This is the claim proved by backward induction in the proof of Proposition 5; Proposition 5 is its case $t=2$ evaluated at $\hat x_1$.
--
--   **Formalization Note** The hypotheses are exactly those of the goal theorem. Infinite values are handled in $\mathbb R\cup\{+\infty\}$: an infeasible stage costs $+\infty$, and $\hat{\mathcal Q}_t$ is $+\infty$ off the convex hull of its points.
-- source:
--   Philpott, de Matos & Finardi, On Solving Multistage Stochastic Programs with Coherent Risk Measures, authors' manuscript of 13 August 2012 (Operations Research, 2013), p. 16, proof of Proposition 5, 'We show by induction that for every x_{t−1} we have ρ_t(v̂_t(x_{t−1}, ω_t)) ≤ 𝒬̂_t(x_{t−1})'

import Mathlib
import Definitions.Def_CoherentSDDP_Inner_Basic
import Definitions.Def_CoherentSDDP_Inner_Model

namespace CoherentSDDP.Inner

theorem induction_claim {n m : ℕ} {Ω : ℕ → Type} [∀ t, Fintype (Ω t)] [∀ t, Nonempty (Ω t)]
    (M : Model n m Ω) (hT : 2 ≤ M.T) (hρ : ∀ t, 2 ≤ t → t ≤ M.T → IsCoherent (M.ρ t))
    (D : InnerData n) (hD : UpperBounds M D)
    (xhat : (t : ℕ) → (Fin n → ℝ) → Ω t → Fin n → ℝ) (x1hat : Fin n → ℝ)
    (hπ : IsInnerPolicy M D xhat x1hat) :
    ∀ t, 2 ≤ t → t ≤ M.T → ∀ xprev : Fin n → ℝ,
      riskE (M.ρ t) (fun ω => vhat M xhat t xprev ω) ≤ Qhat M D t xprev := by sorry

end CoherentSDDP.Inner
