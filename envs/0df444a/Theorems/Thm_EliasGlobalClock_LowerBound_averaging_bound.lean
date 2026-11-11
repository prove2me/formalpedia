-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_averaging_bound
-- name    : EliasGlobalClock.LowerBound.averaging_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:17.078083+00:00
-- url     : https://prove2.me/theorems/2f61ec10-0f66-4a52-be28-0d6b1c998939
-- title:
--   Lemma 4.3 — average over all starting times
-- statement:
--   Fix the parameters and admissible latency guarantee of Lemma 4.2, with $\ell\ge L(n)$. For every integer $T\ge1$,
--
--   $$\frac1T\sum_{t=1}^{T+\ell}\mathbb E_Y\!\left[\sum_{j=1}^{\ell}K(m s_{t\mid Y}(j))\right]\ge\frac12\ln\frac1{\epsilon(n)}.$$
--
--   The column sum is evaluated at a fixed global slot $t$ and includes ages $1,\ldots,\ell$; the outer sum includes $T+\ell$. The statement is uniform in the averaging horizon and retains the source's constant $1/2$.
--
--   Differences from the source:
--   - encoding: anonymous causal GlobalClock rules with private history → wake-indexed Markov kernels on complete all-FAIL binary streams, with independent private streams conditional on the shared input and a constructed stopped execution; reason: running each source rule against perpetual FAIL induces exactly this law; stopping at its first singleton recovers the actual execution; no rule receives population, labels or the schedule
--   - generalization: a common shared random string Y → a shared input with any probability law on any measurable space; reason: random strings with their actual probability law are included by taking the shared space to be the binary sequence space; no finiteness or support restriction is imposed
--   - encoding: L(n,ϵ) at one fixed whole error profile and all spontaneous wake-up patterns → a natural slot budget L(n) at each positive integer n with a strict failure bound for every finite population of size at most n and every first wake-up time; reason: the profile is held fixed throughout the theorem; the at-most-n convention is the population-bound model used on printed p.8; delayed exact-n padding gives the same finite-horizon guarantee
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), printed p.11, PDF p.12, Lemma 4.3, Eq. (4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_contentionModel

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace EliasGlobalClock.LowerBound

/-- Lemma 4.3, printed p.11 / PDF p.12: all slots 1 through T+ℓ. -/
theorem averaging_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (P : StreamProtocol Ω)
    (ε : ℕ+ → ℝ) (L : ℕ+ → ℕ) (hε : ErrorProfile ε) (hL : IsLatency ν P ε L)
    (n : ℕ+) (ℓ m : ℕ) (hℓ : 0 < ℓ) (hm : 2 ≤ m) (heven : Even m)
    (hpop : m * ℓ ≤ (n : ℕ)) (hbudget : L n ≤ ℓ) (T : ℕ) (hT : 1 ≤ T) :
    (1 / 2 : ℝ) * Real.log (1 / ε n) ≤
      (∑ t ∈ Finset.Icc 1 (T + ℓ), ∫ y, columnWeight P t ℓ m y ∂ν) / (T : ℝ) := by sorry

end EliasGlobalClock.LowerBound
