-- Prove2me | Theorems.Thm_FiniteTD_Markov_Supplement_lemma_16
-- name    : FiniteTD.Markov.Supplement.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:43:04.565507+00:00
-- url     : https://prove2.me/theorems/087df942-7899-4b1f-b69c-e36bd07b22ca
-- title:
--   Lemma 16, p. 40 — the TD(λ) mean update points towards θ*: (θ*−θ)⊤x̄(θ) ≥ (1−κ)‖V_θ* − V_θ‖²_D
-- statement:
--   Let $S$ be a finite state space with stochastic matrix $P$ and stationary distribution $\pi$, rewards $R(s,s')$, $\gamma\in[0,1)$, $\lambda\in[0,1]$, and features whose covariance $\Sigma=\sum_s\pi(s)\phi(s)\phi(s)^\top$ has minimum eigenvalue $\omega>0$. Let $T^{(\lambda)}$ be the averaged Bellman operator (28), $\Pi_D$ the $D$-weighted projection onto the span of the features, and $\kappa=\gamma(1-\lambda)/(1-\gamma\lambda)$. Let $V_{\theta^*}=\Phi\theta^*$ be the fixed point $V_{\theta^*}=\Pi_DT^{(\lambda)}V_{\theta^*}$ and $\bar x(\theta)=\Phi^\top D(T^{(\lambda)}\Phi\theta-\Phi\theta)$ the steady-state TD(λ) update. Then for every $\theta\in\mathbb R^d$,
--   $$(\theta^*-\theta)^\top\bar x(\theta)\ge(1-\kappa)\,\|V_{\theta^*}-V_\theta\|_D^2.$$
--
--   This is the TD(λ) analogue of Lemma 3: the expected TD(λ) update is a descent direction for $\|\theta^*-\theta\|_2^2$, with the contraction modulus $\kappa$ of $\Pi_DT^{(\lambda)}$ (Lemma 12) in place of $\gamma$.
--
--   **Formalization Note** $T^{(\lambda)}V=V+\sum_{k\ge0}(\gamma\lambda)^kP^k(r+\gamma PV-V)$, which is (28) for $\lambda<1$ and its limit at $\lambda=1$. $\bar x$ is defined by (39).
--
--   Differences from the source:
--
--   - reading: the discount factor satisfies γ < 1 → 0 ≤ γ < 1; reason: a discount factor is nonnegative; §10 writes γ ∈ [0, 1), and the Cauchy–Schwarz step of Lemma 3 uses γ ≥ 0; the published goal uses the same convention
--   - encoding: rewards are bounded, |R(s, s′)| ≤ rmax → no reward bound is assumed; reason: on the finite state space every reward function is bounded, so the hypothesis excludes no instance and rmax does not occur in the statement
--   - encoding: ω > 0 is the minimum eigenvalue of Σ = Σ_s π(s)φ(s)φ(s)⊤ → ω is the least value of θ⊤Σθ on the Euclidean unit sphere, and 0 < ω; reason: Rayleigh-quotient characterisation of λ_min(Σ); full rank of Σ is 0 < ω
--   - reading: θ* is the unique solution of Φθ = Π_D T_μ^{(λ)} Φθ, with T_μ^{(λ)} given by the series (28) → θ* is any solution of Φθ = Π_D T^{(λ)} Φθ, with T^{(λ)}V = V + Σ_{k≥0}(γλ)^k P^k(r + γPV − V) and Π_D = Φ(Φ⊤DΦ)⁻¹Φ⊤D; reason: for λ < 1 the resolvent form equals (28) after rearranging convergent geometric sums; at λ = 1, which §9 and Algorithm 2 allow, (28) is 0 times a divergent series and the resolvent form is its limit (T^{(1)}V = V_μ), consistent with (38)–(39); uniqueness of the fixed point follows from Lemma 12 and is not assumed
--   - reading: x̄(θ) = lim_t E[δ_t(θ) z_{0:t}], equivalently (38)–(39) → x̄(θ) = Φ⊤D(T^{(λ)}Φθ − Φθ), the right side of (39); reason: the paper states (38) and (39) as equal on p. 38 and uses (39) in Lemma 16; on a finite chain the backward-view series (38) is exactly (39)
--   - generalization: the chain is ergodic with a unique limiting stationary distribution (p. 5); Appendix B additionally assumes Assumption 1 → P is stochastic and π is a stationary distribution; no ergodicity or uniform mixing hypothesis; reason: All source chains satisfy these hypotheses. These particular bounds use the stationary one-step law or deterministic operator/trace bounds, so they also cover periodic and reducible chains; the finite-time bias and Markov convergence bounds in Lemma 20 and Theorem 4 retain Assumption 1.
--   - generalization: features obey ‖φ(s)‖₂ ≤ 1 (p. 6) → no feature-normalization hypothesis; reason: The source normalized features are included. Descent depends on the projected contraction and the full-rank covariance, and does not use the feature norm bound.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 40, Lemma 16 ((28) p. 24, Lemma 12 and κ p. 24, (38)–(39) p. 38; proof via Lemma 21, p. 48)

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_Lambda

namespace FiniteTD.Markov.Supplement

open scoped InnerProductSpace

theorem lemma_16 {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (γ lam : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (ω : ℝ) (θstar : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hω : IsMinEig π φ ω) (hω0 : 0 < ω)
    (hfix : valFn φ θstar = projD π φ (Tlam P γ lam Rw (valFn φ θstar))) :
    ∀ θ : EuclideanSpace ℝ (Fin d),
      (1 - kappa γ lam) * dNormSq π φ (θstar - θ) ≤
        ⟪θstar - θ, xbar π P γ lam Rw φ θ⟫_ℝ := by sorry

end FiniteTD.Markov.Supplement
