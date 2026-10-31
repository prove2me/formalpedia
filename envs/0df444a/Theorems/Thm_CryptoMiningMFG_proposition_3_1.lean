-- Prove2me | Theorems.Thm_CryptoMiningMFG_proposition_3_1
-- name    : CryptoMiningMFG.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:02:09.997993+00:00
-- url     : https://prove2.me/theorems/bb8277b0-1be3-4fe7-8ceb-ecd9dfefd7f9
-- title:
--   Proposition 3.1: the unique CARA equilibrium, $\alpha^*\equiv\bar\alpha^*\equiv\frac{\mathcal K M}{c(1+M)^2}w(r;\gamma)$, and $v=U(x)e^{-\gamma w\mathcal K(T-t)/(1+M)^2}$
-- statement:
--   Consider the mining game with exponential utility $U(x)=-\frac1\gamma e^{-\gamma x}$, $\gamma>0$, parameters $\mathcal K,c,r,M>0$, period $[t_0,T]$, and any law $m_0$ of the miners' initial wealth. Write
--
--   $$
--   a^*=\frac{\mathcal K M}{c(1+M)^2}\,w(r;\gamma),\qquad w(r;\gamma)=\frac{1-e^{-\gamma r}}{\gamma}.
--   $$
--
--   1. **Existence.** The constant $\bar\alpha\equiv a^*$ is an equilibrium mean hash rate.
--   2. **Uniqueness; all miners always active.** Every equilibrium mean hash rate $\bar\alpha$ satisfies, for every $t\in[t_0,T]$ and every $x\in\mathbb R$,
--   $$
--   \alpha^*(t,x;\bar\alpha)=\bar\alpha_t=a^*>0,
--   $$
--   and the individual reward rate (2.2) is
--   $$
--   \lambda_t=\mathcal K\frac{\alpha^*(t,x;\bar\alpha)}{\alpha^*(t,x;\bar\alpha)+M\bar\alpha_t}=\frac{\mathcal K}{1+M}.
--   $$
--   3. **Value function.** For every $t\in[t_0,T]$ and $x\in\mathbb R$,
--   $$
--   v(t,x;a^*)=U(x)\,\exp\!\Big(-\gamma\,w(r;\gamma)\,\frac{\mathcal K(T-t)}{(1+M)^2}\Big),
--   $$
--   and the constant hash rate $a^*$ attains this supremum: under it $\mathbb E[e^{-\gamma X_T}]$ is finite and $-\frac1\gamma\,\mathbb E[e^{-\gamma X_T}]=v(t,x;a^*)$.
--
--   This is one of the few explicit mean field game equilibria outside the linear-quadratic setting: under exponential utility, wealth does not affect hashing, every miner hashes at the same constant rate, and the competition discounts each miner's reward rate to $\mathcal K/(1+M)$.
--
--   Here $v$ is the value function (2.4), the supremum of expected utility over all hash-rate controls of the reward counting process, and an equilibrium is a mean hash rate reproduced, through (2.8), by the law of the wealth of miners following the feedback (2.6).
--
--   Differences from the source:
--   - reading: α*(t, x; ᾱ) is "the optimal hash rate" given by (2.6) on the classical solution v of (2.5), and m(t, x; ᾱ) is "the resulting density of the miners' wealth" (p.11) → α* is formula (2.6) evaluated on the value function (2.4), which is required to be differentiable in x; m(t, ·) is the law of the closed-loop wealth X_t started at time t0 from m0 and driven by a family of controls realizing the feedback α*(s, X_s) for almost every clock path and almost every s; (2.8) integrates α*(t, ·) against that law; reason: this is the paper's definition with v the probabilistic value function instead of an assumed HJB solution; the Fokker–Planck equation (2.11) is the equation that law satisfies and is not imposed separately
--   - reading: "in the equilibrium" and "we find the unique equilibrium (in a given class)" (p.12) → every equilibrium mean hash rate in the sense of §2.5 (any measurable ᾱ positive on [t0, T]) equals a*; reason: the stronger of the two readings; it holds because for exponential utility v(t, ·; ᾱ) has product form for every ᾱ, so the class restriction excludes nothing
--   - reading: r is "the value of the mining reward" (p.9), sign not stated → 0 < r (field r_pos of Model); reason: a reward has positive value; with r ≤ 0 one has w ≤ 0 and no positive mean hash rate exists
--   - generalization: M + 1 is the total number of miners, M a positive integer "assumed large" (p.9) → M any positive real number; reason: nothing in §3.1 uses integrality; every integer M ≥ 1 is an instance
--   - generalization: the initial wealth has a C¹ density m0 with ∫ m0 = 1 (p.11) → the initial wealth law m0 is any probability measure on ℝ; reason: every C¹ probability density defines such a measure
--   - generalization: the supremum in (2.4) is over Markovian controls α_t = α(t, X_t) (p.10) → the supremum is over all non-anticipating controls: measurable, locally integrable hash-rate rules φ_j(s; τ₁,…,τ_j) ≥ 0 of time and of the miner's own reward history; reason: this class contains every Markov control whose closed loop is well defined, and the optimum (the constant rate a*) is Markov, so at the equilibrium the two value functions coincide; for every admissible ᾱ both value functions have the product form U(x)h(t) (translation invariance), so Δv/∂ₓv = w(r;γ) and (2.6) is the same in either class, and so are the equilibria
--   - encoding: E[U(X_T)] with U(x) = −(1/γ)e^{−γx} → −(1/γ) times the lower Lebesgue integral of e^{−γX_T} in [0, ∞], with the integrand set to 0 on the null event of infinitely many rewards by T; the reward process is built from i.i.d. Exp(1) clocks; reason: Lean convention; the event of infinitely many rewards has probability 0 because the intensity is at most 𝒦, so no instance changes
--   - reading: α*(t, x) ≡ a* is "the optimal hash rate" (p.11) of every miner in the equilibrium → besides α* ≡ a*, the constant control a* attains the supremum (2.4) at ᾱ ≡ a*; reason: "optimal" means a control attaining (2.4); stated so that the optimal hash rate is a genuine optimum, not only the formula (2.6)
-- source:
--   Li, Reppen, Sircar, A Mean Field Games Model for Cryptocurrency Mining, arXiv:1912.01952v2 (preprint, 22 Jan 2022), https://arxiv.org/abs/1912.01952v2, Proposition 3.1, p.14, eqs. (3.3), (3.4); proof p.15

import Mathlib
import Definitions.Def_CryptoMiningMFG_IsEquilibrium

open MeasureTheory

namespace CryptoMiningMFG

/-- **Proposition 3.1** of Li, Reppen, Sircar, *A Mean Field Games Model for Cryptocurrency
Mining*, arXiv:1912.01952v2, p.14: "With exponential utility, (3.1), in the equilibrium, all
miners are always active, with constant hash rate α*(t, x) ≡ ᾱ*_t ≡ 𝒦M/(c(1 + M)²) w(r; γ),
(3.3) and their individual reward rate is λ_t ≡ 𝒦/(1 + M), for any t ∈ [t0, T] and x ∈ ℝ. The
value function is given by v(t, x) = U(x) e^{−γ w(r;γ) 𝒦(T−t)/(1+M)²}. (3.4)"

For every model with `𝒦, c, r, γ, M > 0`, `t0 < T`, and every initial wealth law `m0`
(a probability measure), with `a* = 𝒦 M w(r; γ) / (c (1 + M)²)`:
1. (existence) the constant `ᾱ ≡ a*` is an equilibrium mean hash rate;
2. (uniqueness, (3.3) and the reward rate) every equilibrium mean hash rate `ᾱ` satisfies, for
   every `t ∈ [t0, T]`, `ᾱ_t = a*`, and for every `x ∈ ℝ` the optimal hash rate (2.6) is
   `α*(t, x; ᾱ) = a* > 0` and the reward intensity (2.2) at `α*` is
   `𝒦 α* / (α* + M ᾱ_t) = 𝒦 / (1 + M)`;
3. (value function (3.4)) for every `t ∈ [t0, T]` and `x ∈ ℝ`,
   `v(t, x; a*) = U(x) e^{−γ w(r;γ) 𝒦 (T − t)/(1 + M)²}`, and the constant hash rate `a*` attains
   this supremum (its `E[e^{−γ X_T}]` is finite and gives `−(1/γ) E[e^{−γ X_T}] = v(t, x; a*)`). -/
theorem proposition_3_1 (P : Model) (m0 : Measure ℝ) [IsProbabilityMeasure m0] :
    IsEquilibrium P m0 (fun _ => P.aStar) ∧
    (∀ abar : ℝ → ℝ, IsEquilibrium P m0 abar → ∀ t ∈ Set.Icc P.t0 P.T,
      abar t = P.aStar ∧
      ∀ x : ℝ, optRate P abar t x = P.aStar ∧ 0 < optRate P abar t x ∧
        P.K * optRate P abar t x / (optRate P abar t x + P.M * abar t) = P.K / (1 + P.M)) ∧
    (∀ t ∈ Set.Icc P.t0 P.T, ∀ x : ℝ,
      value P t x (fun _ => P.aStar)
          = P.U x * Real.exp (-P.γ * P.w * P.K * (P.T - t) / (1 + P.M) ^ 2) ∧
      costExp P (fun _ => P.aStar) t x (constControl P.aStar) ≠ ⊤ ∧
      -(1 / P.γ) * (costExp P (fun _ => P.aStar) t x (constControl P.aStar)).toReal
          = value P t x (fun _ => P.aStar)) := by sorry

end CryptoMiningMFG
