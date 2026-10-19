-- Prove2me | Theorems.Thm_FiniteTD_Markov_lemma_3
-- name    : FiniteTD.Markov.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:13.963838+00:00
-- url     : https://prove2.me/theorems/08a73ff2-03d6-45e4-bc00-effa72628010
-- title:
--   Lemma 3, p. 11 — the mean TD direction points towards θ*: (θ*−θ)⊤ḡ(θ) ≥ (1−γ)‖V_θ* − V_θ‖²_D
-- statement:
--   Let $P$ be a stochastic matrix on a finite set $S$ with stationary distribution $\pi$, let $R(s,s')$ be transition rewards, $\phi(s)\in\mathbb{R}^d$ features, and $0\le\gamma<1$. Let $\bar g(\theta)=\sum_{s,s'}\pi(s)P(s'\mid s)\big(R(s,s')+\gamma\phi(s')^\top\theta-\phi(s)^\top\theta\big)\phi(s)$ be the steady-state mean TD direction, and let $\theta^*$ satisfy $\bar g(\theta^*)=0$. Then for every $\theta\in\mathbb{R}^d$,
--   $$(\theta^*-\theta)^\top\bar g(\theta)\;\ge\;(1-\gamma)\,\|V_{\theta^*}-V_\theta\|_D^2 .$$
--
--   This quantitative form of Tsitsiklis and Van Roy's descent property is the first-order term of the error recursion (Lemma 8); it also shows that $\theta^*$ is unique when $\Sigma$ has full rank.
--
--   **Formalization Note** The paper only writes $\gamma<1$; the Cauchy–Schwarz step of its proof needs $\gamma\ge0$, which is the paper's standing range $\gamma\in[0,1)$ and is assumed here.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 11, Lemma 3

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting

namespace FiniteTD.Markov

open scoped InnerProductSpace

theorem lemma_3 {S : Type} [Fintype S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (θstar : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hstar : gbar π P γ Rw φ θstar = 0) :
    ∀ θ : EuclideanSpace ℝ (Fin d),
      (1 - γ) * dNormSq π φ (θstar - θ) ≤ ⟪θstar - θ, gbar π P γ Rw φ θ⟫_ℝ := by sorry

end FiniteTD.Markov
