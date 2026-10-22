-- Prove2me | Theorems.Thm_FiniteTD_Markov_theorem_3
-- name    : FiniteTD.Markov.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:08.236484+00:00
-- url     : https://prove2.me/theorems/5b54882f-839b-445a-8b7f-ce7d6acdd39d
-- title:
--   Theorem 3, pp. 17–18 — projected TD(0) under Markov sampling: finite-time bounds (a) 1/√T, (b) exponential to a radius, (c) log T/T
-- statement:
--   Let $S$ be a finite nonempty state space with stochastic matrix $P$ and stationary distribution $\pi$, satisfying Assumption 1 with constants $m>0$, $\rho\in(0,1)$; the chain $s_0,s_1,\dots$ starts from $\pi$. Let $|R(s,s')|\le r_{\max}$, $0\le\gamma<1$, and let the features $\phi(s)\in\mathbb{R}^d$ ($d\ge1$) satisfy $\|\phi(s)\|_2\le1$, with $\omega>0$ the minimum eigenvalue of $\Sigma=\sum_s\pi(s)\phi(s)\phi(s)^\top$. Let $\theta^*$ satisfy $\bar g(\theta^*)=0$, let $R\ge\|\theta^*\|_2$ and $\|\theta_0\|_2\le R$, and run projected TD(0) (20), $\theta_{t+1}=\Pi_{2,R}\big(\theta_t+\alpha_tg_t(\theta_t)\big)$, along the chain. Set $G=r_{\max}+2R$, $\bar\theta_T=T^{-1}\sum_{t=0}^{T-1}\theta_t$, and $\tau_{\mathrm{mix}}(\epsilon)=\min\{t\in\mathbb{N}_0: m\rho^t\le\epsilon\}$. Then:
--
--   1. **(a)** For $T\ge1$ and constant step size $\alpha_0=\dots=\alpha_T=1/\sqrt T$,
--   $$\mathbb{E}\big[\|V_{\theta^*}-V_{\bar\theta_T}\|_D^2\big]\le\frac{\|\theta^*-\theta_0\|_2^2+G^2\big(9+12\tau_{\mathrm{mix}}(1/\sqrt T)\big)}{2\sqrt T(1-\gamma)} .$$
--   2. **(b)** For a constant step size $0<\alpha_0=\dots=\alpha_T<1/(2\omega(1-\gamma))$ and every $T\in\mathbb{N}_0$,
--   $$\mathbb{E}\big[\|\theta^*-\theta_T\|_2^2\big]\le e^{-2\alpha_0(1-\gamma)\omega T}\|\theta^*-\theta_0\|_2^2+\alpha_0\,\frac{G^2\big(9+12\tau_{\mathrm{mix}}(\alpha_0)\big)}{2(1-\gamma)\omega} .$$
--   3. **(c)** For the decaying step sizes $\alpha_t=1/(\omega(t+1)(1-\gamma))$, $t\in\mathbb{N}_0$, and $T\ge1$,
--   $$\mathbb{E}\big[\|V_{\theta^*}-V_{\bar\theta_T}\|_D^2\big]\le\frac{G^2\big(9+24\tau_{\mathrm{mix}}(\alpha_T)\big)}{T(1-\gamma)^2\omega}\,(1+\log T) .$$
--
--   Here $\|V_{\theta^*}-V_\theta\|_D^2=\sum_s\pi(s)\big(\phi(s)^\top(\theta^*-\theta)\big)^2$ and $\mathbb{E}$ is over the stationary trajectory. This is the paper's main result: the first non-asymptotic guarantee for TD(0) with linear function approximation under Markovian observation noise, with rates matching the i.i.d. case up to a mixing-time factor.
--
--   **Formalization Note** The expectation is the finite sum over trajectories $(s_0,\dots,s_T)$ of the chain started from $\pi$; $\bar\theta_T$ averages $\theta_0,\dots,\theta_{T-1}$ as in the text and the proof (Algorithm 1's averaging recursion is a slip). The implicit conditions $T\ge1$ in (a) and (c) (the bounds divide by $\sqrt T$ and $T$) and $\alpha_0>0$ in (b) (so that $\tau_{\mathrm{mix}}(\alpha_0)$ is defined) are explicit, as is $\gamma\ge0$. $\omega$ is characterised as the least value of $\theta^\top\Sigma\theta$ on the unit sphere. $\theta^*$ is any vector with $\bar g(\theta^*)=0$ (unique by Lemma 3). In (a) and (b) the step sizes are constrained only for $t\le T$, as printed; in (c) for all $t$.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, pp. 17–18, Theorem 3 (restated p. 34, proof pp. 34–36)

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting

namespace FiniteTD.Markov

theorem theorem_3 {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {d : ℕ} [NeZero d]
    (P : S → S → ℝ) (π : S → ℝ) (Rw : S → S → ℝ) (rmax γ : ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (ω m ρ R : ℝ) (θstar θ0 : EuclideanSpace ℝ (Fin d))
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hRw : ∀ s s', |Rw s s'| ≤ rmax)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hω : IsMinEig π φ ω) (hω0 : 0 < ω)
    (hstar : gbar π P γ Rw φ θstar = 0) (hA1 : Assumption1 P π m ρ)
    (hR : ‖θstar‖ ≤ R) (hθ0 : ‖θ0‖ ≤ R) :
    -- (a) constant step size 1/√T, averaged iterate
    (∀ T : ℕ, 1 ≤ T → ∀ α : ℕ → ℝ, (∀ t ≤ T, α t = 1 / Real.sqrt T) →
      pathExp π P T (fun w => dNormSq π φ (θstar - avgIter γ Rw φ R α θ0 T (extendPath w))) ≤
        (‖θstar - θ0‖ ^ 2 + (rmax + 2 * R) ^ 2 * (9 + 12 * (tauMix m ρ (1 / Real.sqrt T) : ℝ)))
          / (2 * Real.sqrt T * (1 - γ))) ∧
    -- (b) constant step size α₀ < 1/(2ω(1-γ)), last iterate
    (∀ α0 : ℝ, 0 < α0 → α0 < 1 / (2 * ω * (1 - γ)) →
      ∀ T : ℕ, ∀ α : ℕ → ℝ, (∀ t ≤ T, α t = α0) →
      pathExp π P T (fun w => ‖θstar - ptd γ Rw φ R α θ0 (extendPath w) T‖ ^ 2) ≤
        Real.exp (-2 * α0 * (1 - γ) * ω * T) * ‖θstar - θ0‖ ^ 2
          + α0 * ((rmax + 2 * R) ^ 2 * (9 + 12 * (tauMix m ρ α0 : ℝ)) / (2 * (1 - γ) * ω))) ∧
    -- (c) decaying step size 1/(ω(t+1)(1-γ)), averaged iterate
    (∀ T : ℕ, 1 ≤ T → ∀ α : ℕ → ℝ, (∀ t : ℕ, α t = 1 / (ω * ((t : ℝ) + 1) * (1 - γ))) →
      pathExp π P T (fun w => dNormSq π φ (θstar - avgIter γ Rw φ R α θ0 T (extendPath w))) ≤
        (rmax + 2 * R) ^ 2 * (9 + 24 * (tauMix m ρ (α T) : ℝ)) / (T * (1 - γ) ^ 2 * ω)
          * (1 + Real.log T)) := by sorry

end FiniteTD.Markov
