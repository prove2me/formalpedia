-- Prove2me | Theorems.Thm_CoherentSDDP_Inner_interpolation_bound
-- name    : CoherentSDDP.Inner.interpolation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:45.223486+00:00
-- url     : https://prove2.me/theorems/51f94e4c-de55-492b-b8fd-e04c686a800d
-- title:
--   Proof of Proposition 5, pp. 16–17 — ρ̄ₜ(q_t(x_{t−1}, ω_t)) ≤ 𝒬̂ₜ(x_{t−1}) when the q^i_t bound ρ̄ₜ(q_t(x^i_{t−1}, ·))
-- statement:
--   In the setting of the model file, fix a stage $t$ with $2\le t\le T$ and assume that $\rho_t$ is a coherent risk measure. Suppose the bounds at stage $t$ dominate the risk-adjusted optimal values of the stage problem (13) at their points,
--   $$
--   q^i_t\ \ge\ \bar\rho_t\big(q_t(x^i_{t-1},\omega_t)\big)\qquad\text{for every } i,
--   $$
--   that, if $t<T$, no bound $q^j_{t+1}$ is $-\infty$, and that the stage problem (13) is never unbounded below ($q_t(x,\omega)>-\infty$ for all $x,\omega$). Then for every state $x_{t-1}$,
--   $$
--   \bar\rho_t\big(q_t(x_{t-1},\omega_t)\big)\ \le\ \hat{\mathcal Q}_t(x_{t-1}).
--   $$
--
--   This is the step of the proof of Proposition 5 that uses the inner approximation: the base case at $t=T$ on p. 16 and the "second inequality" on p. 17 for $t<T$. It is the risk-averse form of (9).
--
--   **Formalization Note** The hypothesis $q_t>-\infty$ is added for this lemma; under the hypotheses of the goal theorem it holds because the policy attains the minimum of (13) wherever (13) is feasible. The page writes the last step of the base-case chain as "$=\hat{\mathcal Q}_T(x_{T-1})$"; it is an inequality, and $\le$ is stated. $\bar\rho_t$ is $+\infty$ whenever some outcome has infinite cost.
-- source:
--   Philpott, de Matos & Finardi, On Solving Multistage Stochastic Programs with Coherent Risk Measures, authors' manuscript of 13 August 2012 (Operations Research, 2013), p. 16, proof of Proposition 5, base case; p. 17, proof of Proposition 5, second inequality

import Mathlib
import Definitions.Def_CoherentSDDP_Inner_Basic
import Definitions.Def_CoherentSDDP_Inner_Model

namespace CoherentSDDP.Inner

theorem interpolation_bound {n m : ℕ} {Ω : ℕ → Type} [∀ t, Fintype (Ω t)]
    [∀ t, Nonempty (Ω t)] (M : Model n m Ω) (D : InnerData n) (t : ℕ) (ht : 2 ≤ t)
    (htT : t ≤ M.T) (hρt : IsCoherent (M.ρ t))
    (hDt : ∀ i, riskE (M.ρ t) (fun ω => qstage M D t (D.pts t i) ω) ≤ D.qv t i)
    (hqv : t < M.T → ∀ j, D.qv (t + 1) j ≠ ⊥) (hfin : ∀ x ω, qstage M D t x ω ≠ ⊥) :
    ∀ xprev : Fin n → ℝ,
      riskE (M.ρ t) (fun ω => qstage M D t xprev ω) ≤ Qhat M D t xprev := by sorry

end CoherentSDDP.Inner
