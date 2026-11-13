-- Prove2me | Theorems.Thm_FairReplay_eq_138
-- name    : FairReplay.eq_138
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:48:16.19072+00:00
-- url     : https://prove2.me/theorems/b60f9df1-f6bd-4633-92dd-7700b334a78a
-- title:
--   Eq. (138) — stopped change of measure: $\sum_S\mathbb E_0[N_S]\,I_S\ge\mathrm{kl}(1-\delta,\delta)$
-- statement:
--   Let $\nu_0,\nu_1$ be two sequential-sampling environments on the same finite set of actions (a null and one fixed alternative), and let $\delta\in(0,1/2)$. Let $(\pi,\tau,\psi)$ be a $\delta$-correct tester — any adaptive, possibly randomized policy, any stopping time of the transcript filtration and any decision measurable for the stopped σ-algebra — with finite null expected stopping time $\mathbb E_0[\tau]<\infty$. Write $N_S$ for the number of rounds spent on action $S$ before stopping, and $I_S=D_{\mathrm{KL}}(\nu_{0,S}\,\|\,\nu_{1,S})$ for the one-round information of action $S$. Then
--
--   $$
--   \sum_S\mathbb E_0[N_S]\,I_S\ \ge\ \mathrm{kl}(1-\delta,\delta),
--   \qquad
--   \mathrm{kl}(x,y)=x\log\frac{x}{y}+(1-x)\log\frac{1-x}{1-y}.
--   $$
--
--   This is the adaptive transcript change-of-measure inequality behind both lower bounds of Theorem 10.4, stated for an arbitrary pair of environments so that it can be reused by other sequential-testing results.
--
--   **Formalization Note** Products are in $[0,\infty]$ with $0\cdot\infty=0$, so no absolute-continuity hypothesis is needed. $\mathrm{kl}$ is the published `BanditAlgorithm.bernoulliRelativeEntropy` at $(1-\delta,\delta)\in(0,1)^2$.
--
--   Differences from the source:
--   - encoding: a frozen family of replay actions S, a fixed nuisance η and a fixed alternative a → two arbitrary environments ν₀, ν₁ on k actions; reason: for fixed η and a, P^S_{0,η} and P^S_{a,η} are exactly two such environments
--   - reading: 'the usual stopped-transcript change-of-measure assumptions' and 'every level-δ policy' → τ an IsBanditStoppingTime, ψ measurable for its σ-algebra, IsDeltaCorrect δ, E₀[τ] < ∞, δ ∈ (0, 1/2); reason: the standard assumptions, as in Theorem 10.4's 'finite expected stopping time'; δ < 1/2 is the range of every §10 statement and the bound fails for δ > 1/2 (a policy can randomize its first action and decide on it)
--   - reading: an adaptive tester: actions, stopping time T and accept/reject decision depending on the past transcript → a triple (π, τ, ψ) on the platform's sequential-sampling model: a BanditPolicy over the replay actions, an IsBanditStoppingTime τ (value ⊤ = never stops) and a decision ψ measurable for the stopped σ-algebra; each round's raw ordered outputs are passed as the real number obsCode(outputs); reason: obsCode is injective, so the tester sees the raw ordered transcript; the class is the paper's own 'sequential tester adapted to the independent-round transcript filtration' (Prop. 10.10(i), p.23); randomness outside the transcript (a private seed for τ or ψ) is not modelled, so in the one-action four-way model τ and ψ are functions of the transcript alone
--   - reading: δ-correct: both errors at most δ, for a tester 'terminating with a decision' (Prop. 10.10(i)) → IsDeltaCorrect: P₀(τ < ∞ ∧ reject) ≤ δ and P₁(¬(τ < ∞ ∧ reject)) ≤ δ, so non-stopping counts as a type-II error; reason: every tester that terminates with both errors ≤ δ satisfies it, so the lower bounds cover at least the paper's class; it keeps the never-stopping tester out of the upper bounds and of Q
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), App. E, eqs. (137)–(138), p.34 (PDF p.36); invoked as 'adaptive transcript change of measure followed by data processing' at eq. (41), p.15

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_FairReplay_IsDeltaCorrect
import Definitions.Def_FairReplay_expectedRounds
import Definitions.Def_FairReplay_armCount

open MeasureTheory InformationTheory

namespace FairReplay

/-- **Eq. (138), stopped-transcript change of measure** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027
submission (manuscript of 2026-11-03, sha256 e23940a0…), App. E, eqs. (137)–(138), p.34
(PDF p.36)): "For a frozen family of replay actions S and oriented alternatives a, define the exact
null-to-alternative information I_{a,S}(η) = D_KL(P^S_{0,η} ‖ P^S_{a,η}). (137) Under the usual
stopped-transcript change-of-measure assumptions, every level-δ policy obeys, separately for every
fixed η and a, ∑_S E_{0,η}[N_S] I_{a,S}(η) ≥ kl(1 − δ, δ). (138)"

Let `ν₀, ν₁` be two sequential-sampling environments on the same `k` actions (the null and one
fixed alternative), and `δ ∈ (0, 1/2)`. Every δ-correct tester `(π, τ, ψ)` — any adaptive, possibly
randomized policy, any stopping time of the transcript filtration, any decision measurable for the
stopped σ-algebra — whose null expected stopping time is finite satisfies
`∑ᵢ E₀[Nᵢ] · KL(ν₀ᵢ ‖ ν₁ᵢ) ≥ kl(1 − δ, δ)`, where `Nᵢ` is the number of rounds spent on action `i`
before stopping and `kl(x, y) = x log(x/y) + (1 − x) log((1 − x)/(1 − y))`.

**Formalization Note** The fixed nuisance `η` and alternative `a` of the paper are absorbed in the
choice of `ν₀, ν₁`. The "usual stopped-transcript change-of-measure assumptions" are rendered as:
`τ` a stopping time, `ψ` measurable for its σ-algebra, `E₀[τ] < ∞`. Products are in `ℝ≥0∞`
(`0 · ∞ = 0`), so no absolute-continuity hypothesis is needed. `kl` is the published
`BanditAlgorithm.bernoulliRelativeEntropy`, evaluated at `(1 − δ, δ) ∈ (0, 1)²`. -/
theorem eq_138 {k : ℕ} (ν₀ ν₁ : BanditAlgorithm.StochasticBandit k) (δ : ℝ) (hδ : 0 < δ)
    (hδ2 : δ < 1 / 2) (π : BanditAlgorithm.BanditPolicy k) (τ : (ℕ → Fin k × ℝ) → ℕ∞)
    (ψ : (ℕ → Fin k × ℝ) → Bool) (hτ : BanditAlgorithm.IsBanditStoppingTime τ)
    (hψ : Measurable[hτ.measurableSpace] ψ) (hcorr : IsDeltaCorrect δ ν₀ ν₁ π τ ψ)
    (hfin : expectedRounds ν₀ π τ < ⊤) :
    ENNReal.ofReal (BanditAlgorithm.bernoulliRelativeEntropy (1 - δ) δ) ≤
      ∑ i, (∫⁻ ω, armCount i τ ω ∂BanditAlgorithm.banditTrajMeasure ν₀ π) *
        klDiv (ν₀.P i) (ν₁.P i) := by sorry

end FairReplay
