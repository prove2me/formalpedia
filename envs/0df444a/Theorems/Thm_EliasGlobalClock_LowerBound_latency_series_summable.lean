-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_latency_series_summable
-- name    : EliasGlobalClock.LowerBound.latency_series_summable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:39.619219+00:00
-- url     : https://prove2.me/theorems/afdd2090-ab4d-4bfe-a75b-36e681cb12d6
-- title:
--   Theorem 4.1 — summability of latency across every dyadic scale
-- statement:
--   Fix any randomized anonymous GlobalClock leader-election protocol, allowing a common shared random string and arbitrary private attempt histories. Let $\epsilon:\mathbb Z_+\to(0,1)$ be nonincreasing, and let $L(n,\epsilon)$ be a valid latency profile, uniform over all starting times and spontaneous wake-up patterns with population bounded by $n$. Suppose there is a fixed $\eta\in(0,1)$ such that
--
--   $$\exists C>0\ \exists n_0\ \forall n\ge n_0:\quad
--   \ln(1/\epsilon(n))\le C n^{1-\eta}.$$
--
--   Then
--
--   $$\sum_{i=1}^{\infty}\frac{\ln(1/\epsilon(2^i))}{L(2^i,\epsilon)}<\infty.$$
--
--   The conclusion is actual summability over every dyadic population scale, including scales for which the batch schedule would not be feasible. The paper writes $O(n^{1-\eta})$ in its hypothesis; the constant and eventual cutoff remain existential and uniform. No monotonicity assumption on $L$ is added. This is the necessity statement, independent of the paper's separate protocol and code constructions.
--
--   Differences from the source:
--   - encoding: anonymous causal GlobalClock rules with private history → wake-indexed Markov kernels on complete all-FAIL binary streams, with independent private streams conditional on the shared input and a constructed stopped execution; reason: running each source rule against perpetual FAIL induces exactly this law; stopping at its first singleton recovers the actual execution; no rule receives population, labels or the schedule
--   - generalization: a common shared random string Y → a shared input with any probability law on any measurable space; reason: random strings with their actual probability law are included by taking the shared space to be the binary sequence space; no finiteness or support restriction is imposed
--   - encoding: L(n,ϵ) at one fixed whole error profile and all spontaneous wake-up patterns → a natural slot budget L(n) at each positive integer n with a strict failure bound for every finite population of size at most n and every first wake-up time; reason: the profile is held fixed throughout the theorem; the at-most-n convention is the population-bound model used on printed p.8; delayed exact-n padding gives the same finite-horizon guarantee
--   - encoding: a convergent nonnegative series over i≥1 → Summable of the real sequence indexed by k≥0 at population 2^(k+1); reason: this is a bijective reindexing of the full source series; it is not a bound on a possibly divergent real tsum
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), printed p.8, PDF p.9, Theorem 4.1, Eq. (1); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_contentionModel

open MeasureTheory ProbabilityTheory

namespace EliasGlobalClock.LowerBound

/-- Theorem 4.1, printed p.8 / PDF p.9, full series over every dyadic scale.
L is not assumed monotone. The attained tail-minimum envelope provides an internal
bridge to the monotone windows of Lemma 4.4. No failure or packing lemma, feasible
scale restriction, memorylessness, or finite shared string is a hypothesis. -/
theorem latency_series_summable {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (P : StreamProtocol Ω)
    (ε : ℕ+ → ℝ) (L : ℕ+ → ℕ) (hε : ErrorProfile ε)
    (hL : IsLatency ν P ε L) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (hgrowth : ErrorGrowth ε η) :
    Summable (latencyTerm ε L) := by sorry

end EliasGlobalClock.LowerBound
