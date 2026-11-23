-- Prove2me | Theorems.Thm_FiniteTD_Markov_Supplement_theorem_1
-- name    : FiniteTD.Markov.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:40:46.473169+00:00
-- url     : https://prove2.me/theorems/d9c3475d-4174-4825-bcbb-917b4fd9e1ed
-- title:
--   Theorem 1, p. 12 — mean-path TD: O(1/T) averaged bound and geometric last-iterate bound
-- statement:
--   Let $S$ be a finite state space with stochastic matrix $P$ and stationary distribution $\pi$, rewards $R(s,s')$, discount factor $\gamma\in[0,1)$ and features with $\|\phi(s)\|_2\le1$. Let $\omega>0$ be the minimum eigenvalue of $\Sigma=\sum_s\pi(s)\phi(s)\phi(s)^\top$ and let $\theta^*$ be the TD fixed point, $\bar g(\theta^*)=0$. Consider mean-path TD
--   $$\theta_{t+1}=\theta_t+\alpha\,\bar g(\theta_t),\qquad t\in\mathbb N_0,\qquad \alpha=\frac{1-\gamma}{4},$$
--   from any $\theta_0\in\mathbb R^d$, and let $\bar\theta_T=T^{-1}\sum_{t=0}^{T-1}\theta_t$. Then
--
--   1. for every $T\ge1$, $\displaystyle\|V_{\theta^*}-V_{\bar\theta_T}\|_D^2\le\frac{4\|\theta^*-\theta_0\|_2^2}{T(1-\gamma)^2}$;
--   2. for every $T\in\mathbb N_0$,
--   $$\|\theta^*-\theta_T\|_2^2\le\exp\Big(-\frac{(1-\gamma)^2\omega}{4}\,T\Big)\|\theta^*-\theta_0\|_2^2.$$
--
--   This is the noiseless model of the paper: the same descent and norm properties (Lemmas 3 and 4) that drive the stochastic analyses already give an averaged rate free of the conditioning of $\Sigma$ and a geometric rate governed by $\omega$.
--
--   Differences from the source:
--
--   - reading: the discount factor satisfies γ < 1 → 0 ≤ γ < 1; reason: a discount factor is nonnegative; §10 writes γ ∈ [0, 1), and the Cauchy–Schwarz step of Lemma 3 uses γ ≥ 0; the published goal uses the same convention
--   - encoding: rewards are bounded, |R(s, s′)| ≤ rmax → no reward bound is assumed; reason: on the finite state space every reward function is bounded, so the hypothesis excludes no instance and rmax does not occur in the statement
--   - encoding: θ* is the unique vector with ḡ(θ*) = 0 → θ* is any vector with ḡ(θ*) = 0; reason: Under the source full-rank assumption this names its unique target. The Lean also permits singular feature covariance and any zero of gbar; this larger domain is disclosed below.
--   - encoding: ω > 0 is the minimum eigenvalue of Σ = Σ_s π(s)φ(s)φ(s)⊤ → ω is the least value of θ⊤Σθ on the Euclidean unit sphere, and 0 < ω; reason: Rayleigh-quotient characterisation of λ_min(Σ); full rank of Σ is 0 < ω
--   - encoding: the averaged bound for θ̄_T, whose statement divides by T → the averaged bound is stated for T ≥ 1; reason: θ̄_T and the right side are undefined at T = 0
--   - generalization: the chain is ergodic with a unique limiting stationary distribution (p. 5); Appendix B additionally assumes Assumption 1 → P is stochastic and π is a stationary distribution; no ergodicity or uniform mixing hypothesis; reason: All source chains satisfy these hypotheses. These particular bounds use the stationary one-step law or deterministic operator/trace bounds, so they also cover periodic and reducible chains; the finite-time bias and Markov convergence bounds in Lemma 20 and Theorem 4 retain Assumption 1.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 12, Theorem 1 (mean-path TD defined p. 9, §6)

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_MeanPathIid

namespace FiniteTD.Markov.Supplement

theorem theorem_1 {S : Type} [Fintype S] [Nonempty S] {d : ℕ} [NeZero d]
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (ω : ℝ) (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hω : IsMinEig π φ ω) (hω0 : 0 < ω)
    (hstar : gbar π P γ Rw φ θstar = 0) :
    -- averaged iterate
    (∀ T : ℕ, 1 ≤ T →
      dNormSq π φ (θstar - avgSeq (meanPath π P γ Rw φ ((1 - γ) / 4) θ0) T) ≤
        4 * ‖θstar - θ0‖ ^ 2 / (T * (1 - γ) ^ 2)) ∧
    -- last iterate
    (∀ T : ℕ,
      ‖θstar - meanPath π P γ Rw φ ((1 - γ) / 4) θ0 T‖ ^ 2 ≤
        Real.exp (-((1 - γ) ^ 2 * ω / 4) * T) * ‖θstar - θ0‖ ^ 2) := by sorry

end FiniteTD.Markov.Supplement
