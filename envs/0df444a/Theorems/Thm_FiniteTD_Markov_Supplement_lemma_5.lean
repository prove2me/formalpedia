-- Prove2me | Theorems.Thm_FiniteTD_Markov_Supplement_lemma_5
-- name    : FiniteTD.Markov.Supplement.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:41:12.066807+00:00
-- url     : https://prove2.me/theorems/8e27bd23-55f7-4ebc-bd03-198f090697fd
-- title:
--   Lemma 5, p. 14 — second moment of the TD direction under the stationary tuple law: E‖g_t(θ)‖₂² ≤ 2σ² + 8‖V_θ − V_θ*‖²_D
-- statement:
--   Let $S$ be a finite state space with stochastic matrix $P$ and stationary distribution $\pi$, rewards $R(s,s')$, $\gamma\in[0,1)$, features with $\|\phi(s)\|_2\le1$, and let $\theta^*$ satisfy $\bar g(\theta^*)=0$. In the i.i.d. observation model a tuple $(s_t,R(s_t,s'_t),s'_t)$ equals $(s,R(s,s'),s')$ with probability $\pi(s)P(s'\mid s)$ (15), and $g_t(\theta)=\big(R(s_t,s'_t)+\gamma\phi(s'_t)^\top\theta-\phi(s_t)^\top\theta\big)\phi(s_t)$. With $\sigma^2=\mathbb E\|g_t(\theta^*)\|_2^2$, for every fixed $\theta\in\mathbb R^d$,
--   $$\mathbb E\,\|g_t(\theta)\|_2^2\le2\sigma^2+8\,\|V_\theta-V_{\theta^*}\|_D^2.$$
--
--   This is the stochastic counterpart of Lemma 4 and bounds the second-order term of the TD recursion in the proof of Theorem 2.
--
--   **Formalization Note** The expectation over one tuple with law (15) is the finite sum $\sum_{s,s'}\pi(s)P(s'\mid s)\,\|g(\theta;s,s')\|_2^2$; it does not depend on $t$.
--
--   Differences from the source:
--
--   - reading: the discount factor satisfies γ < 1 → 0 ≤ γ < 1; reason: a discount factor is nonnegative; §10 writes γ ∈ [0, 1), and the Cauchy–Schwarz step of Lemma 3 uses γ ≥ 0; the published goal uses the same convention
--   - encoding: rewards are bounded, |R(s, s′)| ≤ rmax → no reward bound is assumed; reason: on the finite state space every reward function is bounded, so the hypothesis excludes no instance and rmax does not occur in the statement
--   - encoding: θ* is the unique vector with ḡ(θ*) = 0 → θ* is any vector with ḡ(θ*) = 0; reason: Under the source full-rank assumption this names its unique target. The Lean also permits singular feature covariance and any zero of gbar; this larger domain is disclosed below.
--   - encoding: E‖g_t(θ)‖₂² for the random tuple O_t → the finite sum over (s, s′) with weights π(s)P(s′|s); reason: this is the law (15) of O_t on the finite state space
--   - generalization: the chain is ergodic with a unique limiting stationary distribution (p. 5); Appendix B additionally assumes Assumption 1 → P is stochastic and π is a stationary distribution; no ergodicity or uniform mixing hypothesis; reason: All source chains satisfy these hypotheses. These particular bounds use the stationary one-step law or deterministic operator/trace bounds, so they also cover periodic and reducible chains; the finite-time bias and Markov convergence bounds in Lemma 20 and Theorem 4 retain Assumption 1.
--   - generalization: Σ has full rank and the feature columns are independent (pp. 5–6) → no rank or positive-dimension hypothesis; θ* is any zero of gbar; reason: The source target satisfies the Lean hypothesis. The norm and second-moment estimates do not need invertibility, since they compare gbar(θ) with gbar(θ*) or individual TD updates; zero-dimensional parameters are included.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 14, Lemma 5 (model (15) and σ², p. 13)

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_MeanPathIid

namespace FiniteTD.Markov.Supplement

theorem lemma_5 {S : Type} [Fintype S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (θstar : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hstar : gbar π P γ Rw φ θstar = 0) :
    ∀ θ : EuclideanSpace ℝ (Fin d),
      tupleExp π P (fun s s' => ‖tdDir γ Rw φ θ s s'‖ ^ 2) ≤
        2 * sigmaSq π P γ Rw φ θstar + 8 * dNormSq π φ (θ - θstar) := by sorry

end FiniteTD.Markov.Supplement
