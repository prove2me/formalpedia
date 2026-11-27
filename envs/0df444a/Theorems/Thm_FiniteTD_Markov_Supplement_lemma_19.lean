-- Prove2me | Theorems.Thm_FiniteTD_Markov_Supplement_lemma_19
-- name    : FiniteTD.Markov.Supplement.lemma_19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:45:12.035083+00:00
-- url     : https://prove2.me/theorems/d5a8cb9b-d61f-4ef3-9da7-f513196fc87f
-- title:
--   Lemma 19, p. 41 — the TD(λ) error ζ_t: bounded by 2B², 6B-Lipschitz, and trace-truncation bounds
-- statement:
--   Assume the setting of Lemma 18 (finite stationary chain, $|R|\le r_{\max}$, $\gamma\in[0,1)$, $\lambda\in[0,1]$, $\|\phi(s)\|_2\le1$, $\omega>0$, TD(λ) fixed point $\theta^*$ with $\|\theta^*\|_2\le R$) and let $B=(r_{\max}+2R)/(1-\gamma\lambda)$. On a two-sided state path $(\dots,s_{-1},s_0,s_1,\dots)$ let $z_{l:t}=\sum_{k=0}^{t-l}(\gamma\lambda)^k\phi(s_{t-k})$ for integers $l\le t$, $z_{-\infty:t}=\sum_{k\ge0}(\gamma\lambda)^k\phi(s_{t-k})$, and $\zeta_t(\theta,z)=\big(\delta_t(\theta)z-\bar x(\theta)\big)^\top(\theta-\theta^*)$ with $\delta_t$ the TD error of $(s_t,s_{t+1})$. Along every such path, for all $\theta,\theta'\in\Theta_R$:
--
--   1. **(a)** $|\zeta_t(\theta,z_{l:t})|\le2B^2$ for all integers $l\le t$;
--   2. **(b)** $|\zeta_t(\theta,z_{l:t})-\zeta_t(\theta',z_{l:t})|\le6B\,\|\theta-\theta'\|_2$ for all integers $l\le t$;
--   3. **(c)** for every $t\in\mathbb N_0$,
--   $$|\zeta_t(\theta,z_{0:t})-\zeta_t(\theta,z_{t-\tau:t})|\le B^2(\gamma\lambda)^\tau\ \text{ for all }\tau\le t,\qquad |\zeta_t(\theta,z_{0:t})-\zeta_t(\theta,z_{-\infty:t})|\le B^2(\gamma\lambda)^t.$$
--
--   These regularity properties let the bias of TD(λ) be controlled by coupling (Lemma 9): the error is bounded, Lipschitz in the parameter, and insensitive to the distant past of the trace.
--
--   **Formalization Note** The two-sided path is any function from $\mathbb Z$ to $S$; the stationary extension of the chain used in the paper is one such path. The power $(\gamma\lambda)^0$ is $1$ also when $\gamma\lambda=0$.
--
--   Differences from the source:
--
--   - reading: the discount factor satisfies γ < 1 → 0 ≤ γ < 1; reason: a discount factor is nonnegative; §10 writes γ ∈ [0, 1), and the Cauchy–Schwarz step of Lemma 3 uses γ ≥ 0; the published goal uses the same convention
--   - encoding: ω > 0 is the minimum eigenvalue of Σ = Σ_s π(s)φ(s)φ(s)⊤ → ω is the least value of θ⊤Σθ on the Euclidean unit sphere, and 0 < ω; reason: Rayleigh-quotient characterisation of λ_min(Σ); full rank of Σ is 0 < ω
--   - reading: θ* is the unique solution of Φθ = Π_D T_μ^{(λ)} Φθ, with T_μ^{(λ)} given by the series (28) → θ* is any solution of Φθ = Π_D T^{(λ)} Φθ, with T^{(λ)}V = V + Σ_{k≥0}(γλ)^k P^k(r + γPV − V) and Π_D = Φ(Φ⊤DΦ)⁻¹Φ⊤D; reason: for λ < 1 the resolvent form equals (28) after rearranging convergent geometric sums; at λ = 1, which §9 and Algorithm 2 allow, (28) is 0 times a divergent series and the resolvent form is its limit (T^{(1)}V = V_μ), consistent with (38)–(39); uniqueness of the fixed point follows from Lemma 12 and is not assumed
--   - reading: x̄(θ) = lim_t E[δ_t(θ) z_{0:t}], equivalently (38)–(39) → x̄(θ) = Φ⊤D(T^{(λ)}Φθ − Φθ), the right side of (39); reason: the paper states (38) and (39) as equal on p. 38 and uses (39) in Lemma 16; on a finite chain the backward-view series (38) is exactly (39)
--   - generalization: the bound holds with probability 1 → the bound holds for every state path; reason: the inequality is pathwise and uses only the bounds on rewards and features; every path, of positive probability or not, is covered, which specialises to the almost-sure statement
--   - encoding: states (…, s_{−1}, s_0, s_1, …) of a two-sided stationary sequence, windows z_{l:t} for any l ≤ t → any path w : ℤ → S, with integer times l ≤ t in (a), (b) and t ∈ ℕ₀ in (c); reason: the bounds are pathwise; (c) involves z_{0:t}, so t ≥ 0 there
--   - generalization: the chain is ergodic with a unique limiting stationary distribution (p. 5); Appendix B additionally assumes Assumption 1 → P is stochastic and π is a stationary distribution; no ergodicity or uniform mixing hypothesis; reason: All source chains satisfy these hypotheses. These particular bounds use the stationary one-step law or deterministic operator/trace bounds, so they also cover periodic and reducible chains; the finite-time bias and Markov convergence bounds in Lemma 20 and Theorem 4 retain Assumption 1.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 41, Lemma 19 (notation p. 39, proof pp. 46–47)

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_Lambda

namespace FiniteTD.Markov.Supplement

theorem lemma_19 {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ lam : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (ω R : ℝ) (θstar : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hω : IsMinEig π φ ω) (hω0 : 0 < ω)
    (hfix : valFn φ θstar = projD π φ (Tlam P γ lam Rw (valFn φ θstar)))
    (hR : ‖θstar‖ ≤ R) :
    -- (a), (b): any window l ≤ t of a two-sided path
    (∀ (w : ℤ → S) (l t : ℤ), l ≤ t → ∀ θ θ' : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ R → ‖θ'‖ ≤ R →
      |zetaLam π P γ lam Rw φ θstar θ (traceWin φ (γ * lam) w l t) (w t) (w (t + 1))|
          ≤ 2 * ((rmax + 2 * R) / (1 - γ * lam)) ^ 2 ∧
      |zetaLam π P γ lam Rw φ θstar θ (traceWin φ (γ * lam) w l t) (w t) (w (t + 1))
          - zetaLam π P γ lam Rw φ θstar θ' (traceWin φ (γ * lam) w l t) (w t) (w (t + 1))|
          ≤ 6 * ((rmax + 2 * R) / (1 - γ * lam)) * ‖θ - θ'‖) ∧
    -- (c): truncation of the trace
    (∀ (w : ℤ → S) (t : ℕ) (θ : EuclideanSpace ℝ (Fin d)), ‖θ‖ ≤ R →
      (∀ τ : ℕ, τ ≤ t →
        |zetaLam π P γ lam Rw φ θstar θ (traceWin φ (γ * lam) w 0 t) (w t) (w (t + 1))
          - zetaLam π P γ lam Rw φ θstar θ (traceWin φ (γ * lam) w ((t : ℤ) - τ) t) (w t) (w (t + 1))|
          ≤ ((rmax + 2 * R) / (1 - γ * lam)) ^ 2 * (γ * lam) ^ τ) ∧
      |zetaLam π P γ lam Rw φ θstar θ (traceWin φ (γ * lam) w 0 t) (w t) (w (t + 1))
          - zetaLam π P γ lam Rw φ θstar θ (traceInf φ (γ * lam) w t) (w t) (w (t + 1))|
          ≤ ((rmax + 2 * R) / (1 - γ * lam)) ^ 2 * (γ * lam) ^ t) := by sorry

end FiniteTD.Markov.Supplement
