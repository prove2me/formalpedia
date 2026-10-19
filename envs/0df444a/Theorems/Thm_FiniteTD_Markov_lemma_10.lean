-- Prove2me | Theorems.Thm_FiniteTD_Markov_lemma_10
-- name    : FiniteTD.Markov.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:16.160243+00:00
-- url     : https://prove2.me/theorems/a3c63257-fb48-4d52-b538-86e7729d55cf
-- title:
--   Lemma 10, p. 21 — the gradient error ζ_t is bounded by 2G² and 6G-Lipschitz on Θ_R
-- statement:
--   In the setting of Theorem 3 ($P$ stochastic with stationary $\pi$, $|R(s,s')|\le r_{\max}$, $0\le\gamma<1$, $\|\phi(s)\|_2\le1$, $\bar g(\theta^*)=0$, $\|\theta^*\|_2\le R$), let $G=r_{\max}+2R$ and $\Theta_R=\{\theta:\|\theta\|_2\le R\}$. For every transition $(s,s')$, write $\zeta(\theta)=\big(g(\theta;s,s')-\bar g(\theta)\big)^\top(\theta-\theta^*)$. Then for all $\theta,\theta'\in\Theta_R$,
--   $$|\zeta(\theta)|\le 2G^2\qquad\text{and}\qquad|\zeta(\theta)-\zeta(\theta')|\le 6G\,\|\theta-\theta'\|_2 .$$
--
--   Boundedness feeds Lemma 9 (with $\|v\|_\infty\le2G^2$) and the Lipschitz bound lets the proof of Lemma 11 replace $\theta_t$ by the earlier iterate $\theta_{t-\tau}$.
--
--   **Formalization Note** "With probability 1" is stated for every transition $(s,s')$.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 21, Lemma 10 (proof in App. A.3, pp. 36–37)

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting

namespace FiniteTD.Markov

theorem lemma_10 {S : Type} [Fintype S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (R : ℝ) (θstar : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hstar : gbar π P γ Rw φ θstar = 0) (hR : ‖θstar‖ ≤ R) :
    ∀ (s s' : S) (θ θ' : EuclideanSpace ℝ (Fin d)), ‖θ‖ ≤ R → ‖θ'‖ ≤ R →
      |zeta π P γ Rw φ θstar θ s s'| ≤ 2 * (rmax + 2 * R) ^ 2 ∧
      |zeta π P γ Rw φ θstar θ s s' - zeta π P γ Rw φ θstar θ' s s'|
        ≤ 6 * (rmax + 2 * R) * ‖θ - θ'‖ := by sorry

end FiniteTD.Markov
