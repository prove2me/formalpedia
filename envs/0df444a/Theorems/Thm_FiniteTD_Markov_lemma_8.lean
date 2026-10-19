-- Prove2me | Theorems.Thm_FiniteTD_Markov_lemma_8
-- name    : FiniteTD.Markov.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:17.383224+00:00
-- url     : https://prove2.me/theorems/479cb960-d13a-4702-a281-2544c7f6bcdb
-- title:
--   Lemma 8, p. 19 — pathwise error recursion of projected TD(0)
-- statement:
--   Consider the finite Markov reward process with stochastic matrix $P$, stationary distribution $\pi$, rewards $|R(s,s')|\le r_{\max}$, discount $0\le\gamma<1$ and features $\|\phi(s)\|_2\le1$. Let $\theta^*$ satisfy $\bar g(\theta^*)=0$, let $R\ge\|\theta^*\|_2$, $\|\theta_0\|_2\le R$, let the step sizes satisfy $\alpha_t\ge0$, and set $G=r_{\max}+2R$. Let $\theta_t$ be the projected TD(0) iterates (20) along a state path $s_0,s_1,\dots$, and $\zeta_t(\theta)=\big(g_t(\theta)-\bar g(\theta)\big)^\top(\theta-\theta^*)$ with $g_t(\theta)$ the TD direction at the transition $(s_t,s_{t+1})$. Then for every path and every $t\in\mathbb{N}_0$,
--   $$\|\theta^*-\theta_{t+1}\|_2^2\;\le\;\|\theta^*-\theta_t\|_2^2-2\alpha_t(1-\gamma)\|V_{\theta^*}-V_{\theta_t}\|_D^2+2\alpha_t\zeta_t(\theta_t)+\alpha_t^2G^2 .$$
--
--   This is the error decomposition from which all three parts of Theorem 3 follow once the bias term $\mathbb{E}[\zeta_t(\theta_t)]$ is controlled (Lemma 11).
--
--   **Formalization Note** "With probability 1" is stated for every state path. Non-negative step sizes are implicit in the paper (all its step-size rules are positive) and are assumed explicitly.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 19, Lemma 8

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting

namespace FiniteTD.Markov

theorem lemma_8 {S : Type} [Fintype S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (R : ℝ) (α : ℕ → ℝ)
    (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hstar : gbar π P γ Rw φ θstar = 0) (hR : ‖θstar‖ ≤ R) (hθ0 : ‖θ0‖ ≤ R)
    (hα : ∀ t, 0 ≤ α t) :
    ∀ (w : ℕ → S) (t : ℕ),
      ‖θstar - ptd γ Rw φ R α θ0 w (t + 1)‖ ^ 2 ≤
        ‖θstar - ptd γ Rw φ R α θ0 w t‖ ^ 2
          - 2 * α t * (1 - γ) * dNormSq π φ (θstar - ptd γ Rw φ R α θ0 w t)
          + 2 * α t * zeta π P γ Rw φ θstar (ptd γ Rw φ R α θ0 w t) (w t) (w (t + 1))
          + α t ^ 2 * (rmax + 2 * R) ^ 2 := by sorry

end FiniteTD.Markov
