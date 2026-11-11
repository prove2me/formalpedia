-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_failure_probability_bound
-- name    : EliasGlobalClock.LowerBound.failure_probability_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:41.143689+00:00
-- url     : https://prove2.me/theorems/108ed097-0864-42cc-a2a8-ba90c71d6222
-- title:
--   Lemma 4.2 — conditional failure and expected contention weight
-- statement:
--   Fix a protocol, a positive population bound $n$, a positive window length $\ell$, and an even batch size $m\ge2$ with $m\ell\le n$. Wake $m$ players at each slot $t_0,\ldots,t_0+\ell-1$, and let $\mathrm{FAIL}$ mean no singleton in $(t_0,t_0+\ell]$. For every starting time and shared input,
--
--   $$\Pr(\mathrm{FAIL}\mid Y)\ge\exp\!\left(-2\sum_{j=1}^{\ell}K(m s_{t_0+j\mid Y}(j))\right).$$
--
--   In particular, for every admissible error profile $\epsilon$ and valid operational latency $L$, if $\ell\ge L(n)$, then for every $t_0$,
--
--   $$\mathbb E_Y\!\left[\sum_{j=1}^{\ell}K(m s_{t_0+j\mid Y}(j))\right]\ge\frac12\ln\frac1{\epsilon(n)}.$$
--
--   The first clause has no latency premise. Private attempts can be arbitrarily correlated in time; the independent objects are the whole private streams conditional on $Y$. This is the complete two-clause failure lemma.
--
--   Differences from the source:
--   - encoding: anonymous causal GlobalClock rules with private history → wake-indexed Markov kernels on complete all-FAIL binary streams, with independent private streams conditional on the shared input and a constructed stopped execution; reason: running each source rule against perpetual FAIL induces exactly this law; stopping at its first singleton recovers the actual execution; no rule receives population, labels or the schedule
--   - generalization: a common shared random string Y → a shared input with any probability law on any measurable space; reason: random strings with their actual probability law are included by taking the shared space to be the binary sequence space; no finiteness or support restriction is imposed
--   - encoding: L(n,ϵ) at one fixed whole error profile and all spontaneous wake-up patterns → a natural slot budget L(n) at each positive integer n with a strict failure bound for every finite population of size at most n and every first wake-up time; reason: the profile is held fixed throughout the theorem; the at-most-n convention is the population-bound model used on printed p.8; delayed exact-n padding gives the same finite-horizon guarantee
--   - generalization: a conditional failure inequality given Y, understood almost surely → the conditional failure inequality at every shared input y for the normalized stream kernels; reason: the finite-player inequality holds for any fixed normalized private-stream laws, including at null shared inputs; it therefore implies the source almost-sure conditional statement for every source protocol
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), printed p.9, PDF p.10, Lemma 4.2, Eqs. (2)–(3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_contentionModel

open MeasureTheory ProbabilityTheory

namespace EliasGlobalClock.LowerBound

/-- Lemma 4.2, printed p.9 / PDF p.10, both (2) and (3). The first
clause has no latency assumption. The conditional law is constructed, not assumed. -/
theorem failure_probability_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (P : StreamProtocol Ω)
    (n : ℕ+) (ℓ m : ℕ) (hℓ : 0 < ℓ) (hm : 2 ≤ m) (heven : Even m)
    (hpop : m * ℓ ≤ (n : ℕ)) :
    (∀ (t₀ : ℕ) (y : Ω),
      Real.exp (-2 * diagonalWeight P t₀ ℓ m y) ≤
        (privateLaw P (batchWake t₀ ℓ m) y
          (auxiliaryFail (batchWake t₀ ℓ m) t₀ ℓ)).toReal) ∧
    (∀ (ε : ℕ+ → ℝ) (L : ℕ+ → ℕ),
      ErrorProfile ε → IsLatency ν P ε L → L n ≤ ℓ →
      ∀ t₀ : ℕ, (1 / 2 : ℝ) * Real.log (1 / ε n) ≤
        ∫ y, diagonalWeight P t₀ ℓ m y ∂ν) := by sorry

end EliasGlobalClock.LowerBound
