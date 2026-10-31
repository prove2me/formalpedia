-- Prove2me | Theorems.Thm_CryptoMiningMFG_eq_2_10_all_active
-- name    : CryptoMiningMFG.eq_2_10_all_active
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:01:53.87399+00:00
-- url     : https://prove2.me/theorems/ca66ab57-2a70-4481-a5e8-8f90bf30664e
-- title:
--   Eq. (2.10), p.15: every CARA equilibrium is fully active with $\bar\alpha^*_t=\frac{\mathcal K M w}{c(1+M)^2}$
-- statement:
--   Assume exponential utility and let $m_0$ be any initial wealth law (a probability measure). Let $\bar\alpha$ be an equilibrium mean hash rate. Then for every $t\in[t_0,T]$:
--
--   1. every miner is active: $\alpha^*(t,x;\bar\alpha)>0$ for every wealth $x\in\mathbb R$ (so the fraction of active miners is $\eta(t)=1$);
--   2. the mean hash rate is the explicit constant
--   $$
--   \bar\alpha_t=\frac{\mathcal K M}{c(1+M)^2}\,w(r;\gamma).
--   $$
--
--   This is the uniqueness half of Proposition 3.1: the consistency condition (2.8), combined with the wealth independence of $\Delta v/\partial_x v$, leaves exactly one possible mean hash rate.
--
--   Differences from the source:
--   - reading: α*(t, x; ᾱ) is "the optimal hash rate" given by (2.6) on the classical solution v of (2.5), and m(t, x; ᾱ) is "the resulting density of the miners' wealth" (p.11) → α* is formula (2.6) evaluated on the value function (2.4), which is required to be differentiable in x; m(t, ·) is the law of the closed-loop wealth X_t started at time t0 from m0 and driven by a family of controls realizing the feedback α*(s, X_s) for almost every clock path and almost every s; (2.8) integrates α*(t, ·) against that law; reason: this is the paper's definition with v the probabilistic value function instead of an assumed HJB solution; the Fokker–Planck equation (2.11) is the equation that law satisfies and is not imposed separately
--   - reading: "in the equilibrium" and "we find the unique equilibrium (in a given class)" (p.12) → every equilibrium mean hash rate in the sense of §2.5 (any measurable ᾱ positive on [t0, T]) equals a*; reason: the stronger of the two readings; it holds because for exponential utility v(t, ·; ᾱ) has product form for every ᾱ, so the class restriction excludes nothing
--   - reading: r is "the value of the mining reward" (p.9), sign not stated → 0 < r (field r_pos of Model); reason: a reward has positive value; with r ≤ 0 one has w ≤ 0 and no positive mean hash rate exists
--   - generalization: M + 1 is the total number of miners, M a positive integer "assumed large" (p.9) → M any positive real number; reason: nothing in §3.1 uses integrality; every integer M ≥ 1 is an instance
--   - generalization: the initial wealth has a C¹ density m0 with ∫ m0 = 1 (p.11) → the initial wealth law m0 is any probability measure on ℝ; reason: every C¹ probability density defines such a measure
--   - generalization: the supremum in (2.4) is over Markovian controls α_t = α(t, X_t) (p.10) → the supremum is over all non-anticipating controls: measurable, locally integrable hash-rate rules φ_j(s; τ₁,…,τ_j) ≥ 0 of time and of the miner's own reward history; reason: this class contains every Markov control whose closed loop is well defined, and the optimum (the constant rate a*) is Markov, so at the equilibrium the two value functions coincide; for every admissible ᾱ both value functions have the product form U(x)h(t) (translation invariance), so Δv/∂ₓv = w(r;γ) and (2.6) is the same in either class, and so are the equilibria
--   - encoding: E[U(X_T)] with U(x) = −(1/γ)e^{−γx} → −(1/γ) times the lower Lebesgue integral of e^{−γX_T} in [0, ∞], with the integrand set to 0 on the null event of infinitely many rewards by T; the reward process is built from i.i.d. Exp(1) clocks; reason: Lean convention; the event of infinitely many rewards has probability 0 because the intensity is at most 𝒦, so no instance changes
-- source:
--   Li, Reppen, Sircar, A Mean Field Games Model for Cryptocurrency Mining, arXiv:1912.01952v2 (preprint, 22 Jan 2022), https://arxiv.org/abs/1912.01952v2, eq. (2.10) p.12 and proof of Proposition 3.1, p.15 ("Hence, from (2.10), … which means all miners are active and η ≡ 1. The equilibrium mean hash rate is obtained from plugging in the ansatz into (2.10).")

import Mathlib
import Definitions.Def_CryptoMiningMFG_IsEquilibrium

open MeasureTheory

namespace CryptoMiningMFG

/-- **Every CARA equilibrium is fully active at the explicit rate.** Li, Reppen, Sircar,
*A Mean Field Games Model for Cryptocurrency Mining*, arXiv:1912.01952v2, eq. (2.10), p.12, and
proof of Proposition 3.1, p.15: "Hence, from (2.10), ᾱ*_t = η²M/(1 + ηM)² · 𝒦Δv/(c∂ₓv) ≤ … <
𝒦Δv/(Mc∂ₓv), which means all miners are active and η ≡ 1. The equilibrium mean hash rate is
obtained from plugging in the ansatz into (2.10)."

For exponential utility, every initial wealth law `m0` (a probability measure) and every
equilibrium mean hash rate `ᾱ`, for every `t ∈ [t0, T]`: the optimal hash rate (2.6) is positive
at every wealth `x ∈ ℝ`, and `ᾱ_t = 𝒦 M w(r; γ) / (c (1 + M)²)`. -/
theorem eq_2_10_all_active (P : Model) (m0 : Measure ℝ) [IsProbabilityMeasure m0]
    (abar : ℝ → ℝ) (heq : IsEquilibrium P m0 abar) :
    ∀ t ∈ Set.Icc P.t0 P.T, (∀ x : ℝ, 0 < optRate P abar t x) ∧ abar t = P.aStar := by sorry

end CryptoMiningMFG
