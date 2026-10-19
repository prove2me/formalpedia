-- Prove2me | Theorems.Thm_FiniteTD_Markov_lemma_11
-- name    : FiniteTD.Markov.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:15.360493+00:00
-- url     : https://prove2.me/theorems/c81e31a1-26dc-43f2-882d-510aec62533b
-- title:
--   Lemma 11, p. 21 — bound on the gradient bias E[ζ_t(θ_t)]
-- statement:
--   In the setting of Theorem 3 (finite chain with stochastic $P$, stationary start $\pi$ and Assumption 1 with constants $m,\rho$; $|R(s,s')|\le r_{\max}$; $0\le\gamma<1$; $\|\phi(s)\|_2\le1$; $\bar g(\theta^*)=0$; $\|\theta^*\|_2\le R$; $\|\theta_0\|_2\le R$), let $G=r_{\max}+2R$ and let $\theta_t$ be the projected TD(0) iterates (20) along the chain. Let $T\in\mathbb{N}$ and let the step sizes be non-increasing, $\alpha_0\ge\alpha_1\ge\dots\ge\alpha_T>0$. Fix $t<T$ and set $t^*=\max\{0,\,t-\tau_{\mathrm{mix}}(\alpha_T)\}$. Then
--   $$\mathbb{E}[\zeta_t(\theta_t)]\;\le\;G^2\big(4+6\tau_{\mathrm{mix}}(\alpha_T)\big)\,\alpha_{t^*},$$
--   and also
--   $$\mathbb{E}[\zeta_t(\theta_t)]\;\le\;6G^2\sum_{i=0}^{t-1}\alpha_i ,$$
--   where $\zeta_t(\theta_t)=\big(g_t(\theta_t)-\bar g(\theta_t)\big)^\top(\theta_t-\theta^*)$ is evaluated at the transition $(s_t,s_{t+1})$ of the same trajectory that produced $\theta_t$.
--
--   Combined with Lemma 8, this bias bound yields the three rates of Theorem 3.
--
--   **Formalization Note** The expectation is the finite sum over trajectories $(s_0,\dots,s_T)$ of the chain started from $\pi$. $t^*$ is written with natural-number subtraction, which is exactly $\max\{0,t-\tau_{\mathrm{mix}}(\alpha_T)\}$. The condition $\alpha_T>0$ is implicit in the paper (it is needed for $\tau_{\mathrm{mix}}(\alpha_T)$ to be defined) and is assumed explicitly.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 21, Lemma 11 (proof pp. 21–22)

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting

namespace FiniteTD.Markov

theorem lemma_11 {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (m ρ R : ℝ) (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hstar : gbar π P γ Rw φ θstar = 0) (hA1 : Assumption1 P π m ρ)
    (hR : ‖θstar‖ ≤ R) (hθ0 : ‖θ0‖ ≤ R) :
    ∀ (T : ℕ) (α : ℕ → ℝ), (∀ i j, i ≤ j → j ≤ T → α j ≤ α i) → 0 < α T →
      ∀ t < T,
        pathExp π P T (fun w => zeta π P γ Rw φ θstar (ptd γ Rw φ R α θ0 (extendPath w) t)
            (extendPath w t) (extendPath w (t + 1)))
          ≤ (rmax + 2 * R) ^ 2 * (4 + 6 * (tauMix m ρ (α T) : ℝ)) * α (t - tauMix m ρ (α T)) ∧
        pathExp π P T (fun w => zeta π P γ Rw φ θstar (ptd γ Rw φ R α θ0 (extendPath w) t)
            (extendPath w t) (extendPath w (t + 1)))
          ≤ 6 * (rmax + 2 * R) ^ 2 * ∑ i ∈ Finset.range t, α i := by sorry

end FiniteTD.Markov
