-- Prove2me | Theorems.Thm_FiniteTD_Markov_Supplement_theorem_2
-- name    : FiniteTD.Markov.Supplement.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:41:45.73465+00:00
-- url     : https://prove2.me/theorems/e0e164d7-5aa6-4a1e-adda-9de708da7e04
-- title:
--   Theorem 2, p. 13 — TD(0) under the i.i.d. observation model: (a) averaged 1/√T bound, (b) constant step, (c) decaying step
-- statement:
--   Let $S$ be a finite state space with stochastic matrix $P$ and stationary distribution $\pi$, rewards $R(s,s')$, $\gamma\in[0,1)$, features with $\|\phi(s)\|_2\le1$, $\omega>0$ the minimum eigenvalue of $\Sigma=\sum_s\pi(s)\phi(s)\phi(s)^\top$, and $\theta^*$ the TD fixed point, $\bar g(\theta^*)=0$. TD(0) is run from a deterministic $\theta_0$ by $\theta_{t+1}=\theta_t+\alpha_tg_t(\theta_t)$, where the tuples $O_t=(s_t,R(s_t,s'_t),s'_t)$ are independent across $t$, each with law $\pi(s)P(s'\mid s)$ (15). Let $\sigma^2=\mathbb E\|g_t(\theta^*)\|_2^2$ and $\bar\theta_T=T^{-1}\sum_{t=0}^{T-1}\theta_t$.
--
--   1. **(a)** For every $T\ge(8/(1-\gamma))^2$ and step sizes $\alpha_0=\dots=\alpha_T=1/\sqrt T$,
--   $$\mathbb E\,\|V_{\theta^*}-V_{\bar\theta_T}\|_D^2\le\frac{\|\theta^*-\theta_0\|_2^2+2\sigma^2}{\sqrt T(1-\gamma)}.$$
--   2. **(b)** For every constant step size $\alpha_0=\dots=\alpha_T\le\omega(1-\gamma)/8$,
--   $$\mathbb E\,\|\theta^*-\theta_T\|_2^2\le e^{-\alpha_0(1-\gamma)\omega T}\|\theta^*-\theta_0\|_2^2+\alpha_0\,\frac{2\sigma^2}{(1-\gamma)\omega}.$$
--   3. **(c)** For the decaying step sizes $\alpha_t=\beta/(\lambda+t)$, $t\in\mathbb N_0$, with $\beta=\frac{2}{(1-\gamma)\omega}$ and $\lambda=\frac{16}{(1-\gamma)^2\omega}$, for every $T$,
--   $$\mathbb E\,\|\theta^*-\theta_T\|_2^2\le\frac{\nu}{\lambda+T},\qquad \nu=\max\Big\{\frac{8\sigma^2}{(1-\gamma)^2\omega^2},\ \frac{16\|\theta^*-\theta_0\|_2^2}{(1-\gamma)^2\omega}\Big\}.$$
--
--   These three bounds mirror the standard guarantees for stochastic gradient descent: a rate independent of the conditioning of $\Sigma$ for the averaged iterate, geometric forgetting of $\theta_0$ down to a step-size-dependent level, and an $O(1/T)$ rate with knowledge of $\omega$. Here $\lambda$ in (c) is a step-size offset, unrelated to the trace parameter of TD(λ).
--
--   **Formalization Note** Expectations are finite sums over the $T$ independent tuples $O_0,\dots,O_{T-1}$ that determine $\theta_0,\dots,\theta_T$. In (c) the offset $\lambda$ and $\beta$ are written out as $16/((1-\gamma)^2\omega)$ and $2/((1-\gamma)\omega)$.
--
--   Differences from the source:
--
--   - reading: the discount factor satisfies γ < 1 → 0 ≤ γ < 1; reason: a discount factor is nonnegative; §10 writes γ ∈ [0, 1), and the Cauchy–Schwarz step of Lemma 3 uses γ ≥ 0; the published goal uses the same convention
--   - encoding: rewards are bounded, |R(s, s′)| ≤ rmax → no reward bound is assumed; reason: on the finite state space every reward function is bounded, so the hypothesis excludes no instance and rmax does not occur in the statement
--   - encoding: θ* is the unique vector with ḡ(θ*) = 0 → θ* is any vector with ḡ(θ*) = 0; reason: Under the source full-rank assumption this names its unique target. The Lean also permits singular feature covariance and any zero of gbar; this larger domain is disclosed below.
--   - encoding: ω > 0 is the minimum eigenvalue of Σ = Σ_s π(s)φ(s)φ(s)⊤ → ω is the least value of θ⊤Σθ on the Euclidean unit sphere, and 0 < ω; reason: Rayleigh-quotient characterisation of λ_min(Σ); full rank of Σ is 0 < ω
--   - reading: (b): a constant step size α_0 ≤ ω(1 − γ)/8 → 0 ≤ α_0 ≤ ω(1 − γ)/8; reason: step sizes are nonnegative throughout the paper; α_0 = 0 is kept and gives the trivial bound
--   - encoding: the expectation over the i.i.d. tuple sequence (O_t)_{t∈ℕ} → the finite sum over the T tuples O_0, …, O_{T−1}, with the recursion frozen after time T; reason: θ_0, …, θ_T depend only on O_0, …, O_{T−1}, and the tuples are independent with law (15)
--   - generalization: the chain is ergodic with a unique limiting stationary distribution (p. 5); Appendix B additionally assumes Assumption 1 → P is stochastic and π is a stationary distribution; no ergodicity or uniform mixing hypothesis; reason: All source chains satisfy these hypotheses. These particular bounds use the stationary one-step law or deterministic operator/trace bounds, so they also cover periodic and reducible chains; the finite-time bias and Markov convergence bounds in Lemma 20 and Theorem 4 retain Assumption 1.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 13, Theorem 2 (model (15), σ², θ̄_T on p. 13; proof pp. 14–15)

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_MeanPathIid

namespace FiniteTD.Markov.Supplement

theorem theorem_2 {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {d : ℕ} [NeZero d]
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (ω : ℝ) (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hω : IsMinEig π φ ω) (hω0 : 0 < ω)
    (hstar : gbar π P γ Rw φ θstar = 0) :
    -- (a) T ≥ (8/(1-γ))², constant step size 1/√T, averaged iterate
    (∀ T : ℕ, (8 / (1 - γ)) ^ 2 ≤ (T : ℝ) → ∀ α : ℕ → ℝ, (∀ t ≤ T, α t = 1 / Real.sqrt T) →
      iidExp π P T (fun o => dNormSq π φ (θstar - avgSeq (tdIid γ Rw φ α θ0 o) T)) ≤
        (‖θstar - θ0‖ ^ 2 + 2 * sigmaSq π P γ Rw φ θstar) / (Real.sqrt T * (1 - γ))) ∧
    -- (b) constant step size α₀ ≤ ω(1-γ)/8, last iterate
    (∀ α0 : ℝ, 0 ≤ α0 → α0 ≤ ω * (1 - γ) / 8 →
      ∀ T : ℕ, ∀ α : ℕ → ℝ, (∀ t ≤ T, α t = α0) →
      iidExp π P T (fun o => ‖θstar - tdIid γ Rw φ α θ0 o T‖ ^ 2) ≤
        Real.exp (-α0 * (1 - γ) * ω * T) * ‖θstar - θ0‖ ^ 2
          + α0 * (2 * sigmaSq π P γ Rw φ θstar / ((1 - γ) * ω))) ∧
    -- (c) decaying step size β/(λ + t), β = 2/((1-γ)ω), λ = 16/((1-γ)²ω), last iterate
    (∀ α : ℕ → ℝ,
      (∀ t : ℕ, α t = (2 / ((1 - γ) * ω)) / (16 / ((1 - γ) ^ 2 * ω) + t)) →
      ∀ T : ℕ,
      iidExp π P T (fun o => ‖θstar - tdIid γ Rw φ α θ0 o T‖ ^ 2) ≤
        max (8 * sigmaSq π P γ Rw φ θstar / ((1 - γ) ^ 2 * ω ^ 2))
            (16 * ‖θstar - θ0‖ ^ 2 / ((1 - γ) ^ 2 * ω))
          / (16 / ((1 - γ) ^ 2 * ω) + T)) := by sorry

end FiniteTD.Markov.Supplement
