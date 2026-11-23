-- Prove2me | Theorems.Thm_FiniteTD_Markov_Supplement_lemma_4
-- name    : FiniteTD.Markov.Supplement.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:39:57.618481+00:00
-- url     : https://prove2.me/theorems/a646be7d-2f93-4272-ab69-98879f3eaa0f
-- title:
--   Lemma 4, p. 11 — norm of the mean TD direction: ‖ḡ(θ)‖₂ ≤ 2‖V_θ − V_θ*‖_D
-- statement:
--   Let $S$ be a finite state space with stochastic transition matrix $P$ and stationary distribution $\pi$, rewards $R(s,s')$, discount factor $\gamma\in[0,1)$, and features $\phi(s)\in\mathbb R^d$ with $\|\phi(s)\|_2\le1$. Let $\bar g(\theta)=\sum_{s,s'}\pi(s)P(s'\mid s)\big(R(s,s')+\gamma\phi(s')^\top\theta-\phi(s)^\top\theta\big)\phi(s)$ be the steady-state mean TD direction and let $\theta^*$ satisfy $\bar g(\theta^*)=0$. Then for every $\theta\in\mathbb R^d$,
--   $$\|\bar g(\theta)\|_2\le 2\,\|V_\theta-V_{\theta^*}\|_D,$$
--   where $\|V_\theta-V_{\theta^*}\|_D^2=\sum_s\pi(s)\big(\phi(s)^\top(\theta-\theta^*)\big)^2$.
--
--   Together with Lemma 3 this shows that the first-order term of the TD error recursion dominates a multiple of its second-order term; it is the analogue of the gradient bound of smooth convex optimisation used for Theorem 1.
--
--   **Formalization Note** The seminorm $\|V_\theta-V_{\theta^*}\|_D$ is written as the square root of the published `dNormSq`.
--
--   Differences from the source:
--
--   - reading: the discount factor satisfies γ < 1 → 0 ≤ γ < 1; reason: a discount factor is nonnegative; §10 writes γ ∈ [0, 1), and the Cauchy–Schwarz step of Lemma 3 uses γ ≥ 0; the published goal uses the same convention
--   - encoding: rewards are bounded, |R(s, s′)| ≤ rmax → no reward bound is assumed; reason: on the finite state space every reward function is bounded, so the hypothesis excludes no instance and rmax does not occur in the statement
--   - encoding: θ* is the unique vector with ḡ(θ*) = 0 → θ* is any vector with ḡ(θ*) = 0; reason: Under the source full-rank assumption this names its unique target. The Lean also permits singular feature covariance and any zero of gbar; this larger domain is disclosed below.
--   - generalization: the chain is ergodic with a unique limiting stationary distribution (p. 5); Appendix B additionally assumes Assumption 1 → P is stochastic and π is a stationary distribution; no ergodicity or uniform mixing hypothesis; reason: All source chains satisfy these hypotheses. These particular bounds use the stationary one-step law or deterministic operator/trace bounds, so they also cover periodic and reducible chains; the finite-time bias and Markov convergence bounds in Lemma 20 and Theorem 4 retain Assumption 1.
--   - generalization: Σ has full rank and the feature columns are independent (pp. 5–6) → no rank or positive-dimension hypothesis; θ* is any zero of gbar; reason: The source target satisfies the Lean hypothesis. The norm and second-moment estimates do not need invertibility, since they compare gbar(θ) with gbar(θ*) or individual TD updates; zero-dimensional parameters are included.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 11, Lemma 4

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_MeanPathIid

namespace FiniteTD.Markov.Supplement

open scoped InnerProductSpace

theorem lemma_4 {S : Type} [Fintype S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (θstar : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hstar : gbar π P γ Rw φ θstar = 0) :
    ∀ θ : EuclideanSpace ℝ (Fin d),
      ‖gbar π P γ Rw φ θ‖ ≤ 2 * Real.sqrt (dNormSq π φ (θ - θstar)) := by sorry

end FiniteTD.Markov.Supplement
