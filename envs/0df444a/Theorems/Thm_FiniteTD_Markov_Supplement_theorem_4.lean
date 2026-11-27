-- Prove2me | Theorems.Thm_FiniteTD_Markov_Supplement_theorem_4
-- name    : FiniteTD.Markov.Supplement.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:46:33.665492+00:00
-- url     : https://prove2.me/theorems/0ebabcc3-c8f9-4018-aa26-e6d577f002bb
-- title:
--   Theorem 4, p. 25 — projected TD(λ) under Markov sampling: (a) 1/√T, (b) exponential to a radius, (c) log T/T
-- statement:
--   Let $S$ be a finite state space with stochastic matrix $P$ and stationary distribution $\pi$ satisfying Assumption 1 with constants $m>0$, $\rho\in(0,1)$, the chain started from $\pi$. Let $|R(s,s')|\le r_{\max}$, $\gamma\in[0,1)$, $\lambda\in[0,1]$, features with $\|\phi(s)\|_2\le1$ whose covariance $\Sigma$ has minimum eigenvalue $\omega>0$, and let $\theta^*$ be the TD(λ) fixed point $\Phi\theta^*=\Pi_DT^{(\lambda)}\Phi\theta^*$. Projected TD(λ) (Algorithm 2) is run with radius $R\ge\|\theta^*\|_2$ from $\|\theta_0\|_2\le R$:
--   $$z_{0:t}=\sum_{k=0}^t(\gamma\lambda)^k\phi(s_{t-k}),\qquad \theta_{t+1}=\Pi_{2,R}\big(\theta_t+\alpha_t\,\delta_t(\theta_t)\,z_{0:t}\big).$$
--   Let $B=(r_{\max}+2R)/(1-\gamma\lambda)$, $\kappa=\gamma(1-\lambda)/(1-\gamma\lambda)$, $\tau^{\mathrm{mix}}_\lambda$ the mixing time (30), and $\bar\theta_T=T^{-1}\sum_{t=0}^{T-1}\theta_t$. Then:
--
--   1. **(a)** with $\alpha_t=\alpha_0=1/\sqrt T$,
--   $$\mathbb E\,\|V_{\theta^*}-V_{\bar\theta_T}\|_D^2\le\frac{\|\theta^*-\theta_0\|_2^2+B^2\big(13+28\,\tau^{\mathrm{mix}}_\lambda(1/\sqrt T)\big)}{2\sqrt T(1-\kappa)};$$
--   2. **(b)** with $\alpha_t=\alpha_0<1/(2\omega(1-\kappa))$ and $T>2\tau^{\mathrm{mix}}_\lambda(\alpha_0)$,
--   $$\mathbb E\,\|\theta^*-\theta_T\|_2^2\le e^{-2\alpha_0(1-\kappa)\omega T}\|\theta^*-\theta_0\|_2^2+\alpha_0\,\frac{B^2\big(13+24\,\tau^{\mathrm{mix}}_\lambda(\alpha_0)\big)}{2(1-\kappa)\omega};$$
--   3. **(c)** with $\alpha_t=1/(\omega(t+1)(1-\kappa))$,
--   $$\mathbb E\,\|V_{\theta^*}-V_{\bar\theta_T}\|_D^2\le\frac{B^2\big(13+52\,\tau^{\mathrm{mix}}_\lambda(\alpha_T)\big)}{T(1-\kappa)^2\omega}\,(1+\log T).$$
--
--   These are the first non-asymptotic guarantees for TD(λ); compared with Theorem 3 the contraction factor improves from $\gamma$ to $\kappa$, while the noise scale grows from $G=r_{\max}+2R$ to $B$.
--
--   **Formalization Note** Expectations are finite sums over the trajectory $s_0,\dots,s_T$ of the stationary chain. In (a) and (c), $T\ge1$; in (b), $\alpha_0>0$. The step-size hypotheses are imposed on $\alpha_0,\dots,\alpha_T$ in (a), (b) and on all $t$ in (c).
--
--   Differences from the source:
--
--   - reading: the discount factor satisfies γ < 1 → 0 ≤ γ < 1; reason: a discount factor is nonnegative; §10 writes γ ∈ [0, 1), and the Cauchy–Schwarz step of Lemma 3 uses γ ≥ 0; the published goal uses the same convention
--   - encoding: ω > 0 is the minimum eigenvalue of Σ = Σ_s π(s)φ(s)φ(s)⊤ → ω is the least value of θ⊤Σθ on the Euclidean unit sphere, and 0 < ω; reason: Rayleigh-quotient characterisation of λ_min(Σ); full rank of Σ is 0 < ω
--   - reading: θ* is the unique solution of Φθ = Π_D T_μ^{(λ)} Φθ, with T_μ^{(λ)} given by the series (28) → θ* is any solution of Φθ = Π_D T^{(λ)} Φθ, with T^{(λ)}V = V + Σ_{k≥0}(γλ)^k P^k(r + γPV − V) and Π_D = Φ(Φ⊤DΦ)⁻¹Φ⊤D; reason: for λ < 1 the resolvent form equals (28) after rearranging convergent geometric sums; at λ = 1, which §9 and Algorithm 2 allow, (28) is 0 times a divergent series and the resolvent form is its limit (T^{(1)}V = V_μ), consistent with (38)–(39); uniqueness of the fixed point follows from Lemma 12 and is not assumed
--   - reading: the averaged iterate: Algorithm 2 updates θ̄_{t+1} = (1/(t+1)) Σ_{ℓ=1}^{t+1} θ_ℓ → θ̄_T = T⁻¹ Σ_{t=0}^{T−1} θ_t; reason: this is the average defined on p. 6 and the one the proof sums (pp. 43–45, Jensen over t = 0, …, T − 1); the published goal uses the same convention
--   - encoding: (a), (c): bounds with 1/√T, division by T and log T → T ≥ 1; reason: the quantities are undefined at T = 0
--   - reading: (b): a constant step size α_0 < 1/(2ω(1 − κ)) → 0 < α_0 < 1/(2ω(1 − κ)); reason: step sizes are nonnegative and τmix_λ(α_0) is only defined for α_0 > 0
--   - encoding: E over the stationary Markov chain with Assumption 1 → the finite sum over trajectories s_0, …, s_T started from π; reason: θ_0, …, θ_T depend only on s_0, …, s_T; this is their exact law on a finite state space
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 25, Theorem 4 (restated pp. 38–39; proof pp. 43–45; (28) p. 24, (30) p. 25)

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_MeanPathIid
import Definitions.Def_FiniteTD_Markov_Supplement_Lambda

namespace FiniteTD.Markov.Supplement

theorem theorem_4 {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {d : ℕ} [NeZero d]
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ lam : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (ω m ρ R : ℝ) (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hω : IsMinEig π φ ω) (hω0 : 0 < ω)
    (hfix : valFn φ θstar = projD π φ (Tlam P γ lam Rw (valFn φ θstar)))
    (hA1 : Assumption1 P π m ρ) (hR : ‖θstar‖ ≤ R) (hθ0 : ‖θ0‖ ≤ R) :
    -- (a) constant step size 1/√T, averaged iterate
    (∀ T : ℕ, 1 ≤ T → ∀ α : ℕ → ℝ, (∀ t ≤ T, α t = 1 / Real.sqrt T) →
      pathExp π P T (fun w =>
          dNormSq π φ (θstar - avgSeq (ptdLam γ lam Rw φ R α θ0 (extendPath w)) T)) ≤
        (‖θstar - θ0‖ ^ 2 + ((rmax + 2 * R) / (1 - γ * lam)) ^ 2
            * (13 + 28 * (tauMixLam m ρ (γ * lam) (1 / Real.sqrt T) : ℝ)))
          / (2 * Real.sqrt T * (1 - kappa γ lam))) ∧
    -- (b) constant step size α₀ < 1/(2ω(1-κ)) and T > 2τmix_λ(α₀), last iterate
    (∀ α0 : ℝ, 0 < α0 → α0 < 1 / (2 * ω * (1 - kappa γ lam)) →
      ∀ T : ℕ, 2 * tauMixLam m ρ (γ * lam) α0 < T → ∀ α : ℕ → ℝ, (∀ t ≤ T, α t = α0) →
      pathExp π P T (fun w => ‖θstar - ptdLam γ lam Rw φ R α θ0 (extendPath w) T‖ ^ 2) ≤
        Real.exp (-2 * α0 * (1 - kappa γ lam) * ω * T) * ‖θstar - θ0‖ ^ 2
          + α0 * (((rmax + 2 * R) / (1 - γ * lam)) ^ 2
              * (13 + 24 * (tauMixLam m ρ (γ * lam) α0 : ℝ)) / (2 * (1 - kappa γ lam) * ω))) ∧
    -- (c) decaying step size 1/(ω(t+1)(1-κ)), averaged iterate
    (∀ T : ℕ, 1 ≤ T → ∀ α : ℕ → ℝ,
      (∀ t : ℕ, α t = 1 / (ω * ((t : ℝ) + 1) * (1 - kappa γ lam))) →
      pathExp π P T (fun w =>
          dNormSq π φ (θstar - avgSeq (ptdLam γ lam Rw φ R α θ0 (extendPath w)) T)) ≤
        ((rmax + 2 * R) / (1 - γ * lam)) ^ 2
            * (13 + 52 * (tauMixLam m ρ (γ * lam) (α T) : ℝ)) / (T * (1 - kappa γ lam) ^ 2 * ω)
          * (1 + Real.log T)) := by sorry

end FiniteTD.Markov.Supplement
