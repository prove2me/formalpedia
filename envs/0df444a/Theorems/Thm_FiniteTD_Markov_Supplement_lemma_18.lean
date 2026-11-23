-- Prove2me | Theorems.Thm_FiniteTD_Markov_Supplement_lemma_18
-- name    : FiniteTD.Markov.Supplement.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:43:57.767201+00:00
-- url     : https://prove2.me/theorems/d8951b7f-0e44-40d1-9c70-de503b16b08c
-- title:
--   Lemma 18, p. 40 — pathwise error recursion of projected TD(λ)
-- statement:
--   Let $S$ be a finite state space with stochastic matrix $P$ and stationary distribution $\pi$, rewards with $|R(s,s')|\le r_{\max}$, $\gamma\in[0,1)$, $\lambda\in[0,1]$, features with $\|\phi(s)\|_2\le1$ whose covariance has minimum eigenvalue $\omega>0$, and let $\theta^*$ be the TD(λ) fixed point, $\Phi\theta^*=\Pi_DT^{(\lambda)}\Phi\theta^*$, with $\|\theta^*\|_2\le R$. Run projected TD(λ) $\theta_{t+1}=\Pi_{2,R}\big(\theta_t+\alpha_t\delta_t(\theta_t)z_{0:t}\big)$ from $\|\theta_0\|_2\le R$ with nonnegative step sizes, and set $B=(r_{\max}+2R)/(1-\gamma\lambda)$ and $\kappa=\gamma(1-\lambda)/(1-\gamma\lambda)$. Then along every state path and for every $t\in\mathbb N_0$,
--   $$\|\theta^*-\theta_{t+1}\|_2^2\le\|\theta^*-\theta_t\|_2^2-2\alpha_t(1-\kappa)\|V_{\theta^*}-V_{\theta_t}\|_D^2+2\alpha_t\zeta_t(\theta_t,z_{0:t})+\alpha_t^2B^2,$$
--   where $\zeta_t(\theta,z)=\big(\delta_t(\theta)z-\bar x(\theta)\big)^\top(\theta-\theta^*)$ (40).
--
--   This is the error decomposition of the TD(λ) analysis: the descent term comes from Lemma 16, the noise term from Lemma 17, and all the difficulty is moved into the bias term $\zeta_t$.
--
--   Differences from the source:
--
--   - reading: the discount factor satisfies γ < 1 → 0 ≤ γ < 1; reason: a discount factor is nonnegative; §10 writes γ ∈ [0, 1), and the Cauchy–Schwarz step of Lemma 3 uses γ ≥ 0; the published goal uses the same convention
--   - encoding: ω > 0 is the minimum eigenvalue of Σ = Σ_s π(s)φ(s)φ(s)⊤ → ω is the least value of θ⊤Σθ on the Euclidean unit sphere, and 0 < ω; reason: Rayleigh-quotient characterisation of λ_min(Σ); full rank of Σ is 0 < ω
--   - reading: θ* is the unique solution of Φθ = Π_D T_μ^{(λ)} Φθ, with T_μ^{(λ)} given by the series (28) → θ* is any solution of Φθ = Π_D T^{(λ)} Φθ, with T^{(λ)}V = V + Σ_{k≥0}(γλ)^k P^k(r + γPV − V) and Π_D = Φ(Φ⊤DΦ)⁻¹Φ⊤D; reason: for λ < 1 the resolvent form equals (28) after rearranging convergent geometric sums; at λ = 1, which §9 and Algorithm 2 allow, (28) is 0 times a divergent series and the resolvent form is its limit (T^{(1)}V = V_μ), consistent with (38)–(39); uniqueness of the fixed point follows from Lemma 12 and is not assumed
--   - reading: x̄(θ) = lim_t E[δ_t(θ) z_{0:t}], equivalently (38)–(39) → x̄(θ) = Φ⊤D(T^{(λ)}Φθ − Φθ), the right side of (39); reason: the paper states (38) and (39) as equal on p. 38 and uses (39) in Lemma 16; on a finite chain the backward-view series (38) is exactly (39)
--   - generalization: the bound holds with probability 1 → the bound holds for every state path; reason: the inequality is pathwise and uses only the bounds on rewards and features; every path, of positive probability or not, is covered, which specialises to the almost-sure statement
--   - reading: step sizes α_t (sign not stated) → α_t ≥ 0 for every t; reason: step sizes are nonnegative in the paper, and the descent step through Lemma 16 multiplies an inequality by α_t
--   - generalization: the chain is ergodic with a unique limiting stationary distribution (p. 5); Appendix B additionally assumes Assumption 1 → P is stochastic and π is a stationary distribution; no ergodicity or uniform mixing hypothesis; reason: All source chains satisfy these hypotheses. These particular bounds use the stationary one-step law or deterministic operator/trace bounds, so they also cover periodic and reducible chains; the finite-time bias and Markov convergence bounds in Lemma 20 and Theorem 4 retain Assumption 1.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 40, Lemma 18 ((40) p. 39)

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_Lambda

namespace FiniteTD.Markov.Supplement

theorem lemma_18 {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ lam : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (ω R : ℝ) (α : ℕ → ℝ)
    (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hω : IsMinEig π φ ω) (hω0 : 0 < ω)
    (hfix : valFn φ θstar = projD π φ (Tlam P γ lam Rw (valFn φ θstar)))
    (hR : ‖θstar‖ ≤ R) (hθ0 : ‖θ0‖ ≤ R) (hα : ∀ t, 0 ≤ α t) :
    ∀ (w : ℕ → S) (t : ℕ),
      ‖θstar - ptdLam γ lam Rw φ R α θ0 w (t + 1)‖ ^ 2 ≤
        ‖θstar - ptdLam γ lam Rw φ R α θ0 w t‖ ^ 2
          - 2 * α t * (1 - kappa γ lam) * dNormSq π φ (θstar - ptdLam γ lam Rw φ R α θ0 w t)
          + 2 * α t * zetaLam π P γ lam Rw φ θstar (ptdLam γ lam Rw φ R α θ0 w t)
              (traceN φ (γ * lam) w t) (w t) (w (t + 1))
          + α t ^ 2 * ((rmax + 2 * R) / (1 - γ * lam)) ^ 2 := by sorry

end FiniteTD.Markov.Supplement
