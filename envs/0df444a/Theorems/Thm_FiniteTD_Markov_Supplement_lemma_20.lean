-- Prove2me | Theorems.Thm_FiniteTD_Markov_Supplement_lemma_20
-- name    : FiniteTD.Markov.Supplement.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:45:57.100822+00:00
-- url     : https://prove2.me/theorems/a4fff7b6-5bcd-40a5-97c9-ee929188a9a1
-- title:
--   Lemma 20, p. 41 — bounds on the TD(λ) gradient bias E[ζ_t(θ_t, z_{0:t})]: (a) late times, (b) early times, (c) all times
-- statement:
--   Assume the setting of Lemma 18 and Assumption 1 (constants $m>0$, $\rho\in(0,1)$, stationary start $s_0\sim\pi$). Let $B=(r_{\max}+2R)/(1-\gamma\lambda)$, let $\tau^{\mathrm{mix}}_\lambda$ be the TD(λ) mixing time (30), and let $\theta_t$ be projected TD(λ) from $\|\theta_0\|_2\le R$ along the stationary chain, with $\zeta_t(\theta,z)$ as in (40).
--
--   1. For a non-increasing step-size sequence $\alpha_0\ge\alpha_1\ge\dots\ge\alpha_T$ with $\alpha_T>0$, and $\tau=\tau^{\mathrm{mix}}_\lambda(\alpha_T)$:
--      - **(a)** for $2\tau<t\le T$, $\ \mathbb E[\zeta_t(\theta_t,z_{0:t})]\le6B^2(1+2\tau)\,\alpha_{t-2\tau}$;
--      - **(b)** for $0\le t\le2\tau$ (and $t\le T$), $\ \mathbb E[\zeta_t(\theta_t,z_{0:t})]\le6B^2(1+2\tau)\,\alpha_0+B^2(\gamma\lambda)^t$.
--   2. **(c)** For all $t\in\mathbb N_0$ (and any nonnegative step sizes),
--   $$\mathbb E[\zeta_t(\theta_t,z_{0:t})]\le6B^2\sum_{i=0}^{t-1}\alpha_i+B^2(\gamma\lambda)^t.$$
--
--   This lemma is the core of the TD(λ) analysis: the bias created by the dependence between the iterate, the trace and the current transition is of the order of the step size times the mixing time, plus a transient from the trace's zero start.
--
--   **Formalization Note** $\mathbb E[\zeta_t(\theta_t,z_{0:t})]$ is the expectation over $s_0,\dots,s_{t+1}$ of the stationary chain, a finite sum over trajectories. In (a) the index $t-2\tau$ is a natural number because $t>2\tau$.
--
--   The horizon convention in (b) follows the finite step list fixed on p. 39 and the estimate on p. 43; no bound is asserted for an unspecified continuation beyond that horizon.
--
--   Differences from the source:
--
--   - reading: the discount factor satisfies γ < 1 → 0 ≤ γ < 1; reason: a discount factor is nonnegative; §10 writes γ ∈ [0, 1), and the Cauchy–Schwarz step of Lemma 3 uses γ ≥ 0; the published goal uses the same convention
--   - encoding: ω > 0 is the minimum eigenvalue of Σ = Σ_s π(s)φ(s)φ(s)⊤ → ω is the least value of θ⊤Σθ on the Euclidean unit sphere, and 0 < ω; reason: Rayleigh-quotient characterisation of λ_min(Σ); full rank of Σ is 0 < ω
--   - reading: θ* is the unique solution of Φθ = Π_D T_μ^{(λ)} Φθ, with T_μ^{(λ)} given by the series (28) → θ* is any solution of Φθ = Π_D T^{(λ)} Φθ, with T^{(λ)}V = V + Σ_{k≥0}(γλ)^k P^k(r + γPV − V) and Π_D = Φ(Φ⊤DΦ)⁻¹Φ⊤D; reason: for λ < 1 the resolvent form equals (28) after rearranging convergent geometric sums; at λ = 1, which §9 and Algorithm 2 allow, (28) is 0 times a divergent series and the resolvent form is its limit (T^{(1)}V = V_μ), consistent with (38)–(39); uniqueness of the fixed point follows from Lemma 12 and is not assumed
--   - reading: x̄(θ) = lim_t E[δ_t(θ) z_{0:t}], equivalently (38)–(39) → x̄(θ) = Φ⊤D(T^{(λ)}Φθ − Φθ), the right side of (39); reason: the paper states (38) and (39) as equal on p. 38 and uses (39) in Lemma 16; on a finite chain the backward-view series (38) is exactly (39)
--   - encoding: E over the stationary Markov chain with Assumption 1 → the finite sum over trajectories s_0, …, s_{t+1} started from π; reason: the law of the first t + 2 states of the stationary chain on a finite state space
--   - reading: (b): 0 ≤ t ≤ 2τmix_λ(α_T), for the sequence α_0 ≥ ⋯ ≥ α_T → 0 ≤ t ≤ 2τmix_λ(α_T) and t ≤ T; reason: Appendix B.1, p. 39, fixes the finite horizon and step list (α0,…,αT). The p. 43 proof uses Σ_{i<t} α_i ≤ t α0. The bound is asserted for in-horizon iterates t ≤ T; an out-of-horizon continuation of a finite list is not specified. This boundary interpretation preserves all iterates in the stated finite-horizon problem.
--   - generalization: (c): for all t ∈ ℕ₀, under the non-increasing sequence α_0 ≥ ⋯ ≥ α_T → for every t and every sequence of nonnegative step sizes; reason: Equations (45)–(46), p. 43, give this bound for every t using only the nonnegative steps actually used before t. The Lean permits any globally nonnegative sequence, including every globally nonincreasing positive source step sequence, without a horizon restriction on (c).
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 41, Lemma 20 ((30) p. 25, Assumption 1 p. 16; proof pp. 41–43)

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting
import Definitions.Def_FiniteTD_Markov_Supplement_Lambda

namespace FiniteTD.Markov.Supplement

theorem lemma_20 {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ lam : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (ω m ρ R : ℝ) (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hω : IsMinEig π φ ω) (hω0 : 0 < ω)
    (hfix : valFn φ θstar = projD π φ (Tlam P γ lam Rw (valFn φ θstar)))
    (hA1 : Assumption1 P π m ρ) (hR : ‖θstar‖ ≤ R) (hθ0 : ‖θ0‖ ≤ R) :
    -- (a), (b): a non-increasing step-size sequence α₀ ≥ ⋯ ≥ α_T with α_T > 0
    (∀ (T : ℕ) (α : ℕ → ℝ), (∀ i j, i ≤ j → j ≤ T → α j ≤ α i) → 0 < α T →
      (∀ t : ℕ, 2 * tauMixLam m ρ (γ * lam) (α T) < t → t ≤ T →
        pathExp π P (t + 1) (fun w => zetaLam π P γ lam Rw φ θstar
            (ptdLam γ lam Rw φ R α θ0 (extendPath w) t)
            (traceN φ (γ * lam) (extendPath w) t) (extendPath w t) (extendPath w (t + 1)))
          ≤ 6 * ((rmax + 2 * R) / (1 - γ * lam)) ^ 2
              * (1 + 2 * (tauMixLam m ρ (γ * lam) (α T) : ℝ))
              * α (t - 2 * tauMixLam m ρ (γ * lam) (α T))) ∧
      (∀ t : ℕ, t ≤ 2 * tauMixLam m ρ (γ * lam) (α T) → t ≤ T →
        pathExp π P (t + 1) (fun w => zetaLam π P γ lam Rw φ θstar
            (ptdLam γ lam Rw φ R α θ0 (extendPath w) t)
            (traceN φ (γ * lam) (extendPath w) t) (extendPath w t) (extendPath w (t + 1)))
          ≤ 6 * ((rmax + 2 * R) / (1 - γ * lam)) ^ 2
              * (1 + 2 * (tauMixLam m ρ (γ * lam) (α T) : ℝ)) * α 0
            + ((rmax + 2 * R) / (1 - γ * lam)) ^ 2 * (γ * lam) ^ t)) ∧
    -- (c): every t, any nonnegative step sizes
    (∀ α : ℕ → ℝ, (∀ i, 0 ≤ α i) → ∀ t : ℕ,
      pathExp π P (t + 1) (fun w => zetaLam π P γ lam Rw φ θstar
          (ptdLam γ lam Rw φ R α θ0 (extendPath w) t)
          (traceN φ (γ * lam) (extendPath w) t) (extendPath w t) (extendPath w (t + 1)))
        ≤ 6 * ((rmax + 2 * R) / (1 - γ * lam)) ^ 2 * ∑ i ∈ Finset.range t, α i
          + ((rmax + 2 * R) / (1 - γ * lam)) ^ 2 * (γ * lam) ^ t) := by sorry

end FiniteTD.Markov.Supplement
