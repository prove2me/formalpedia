-- Prove2me | Theorems.Thm_DistributedMWC440_UpperBound_lemma_7_5
-- name    : DistributedMWC440.UpperBound.lemma_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:26:04.002916+00:00
-- url     : https://prove2.me/theorems/555e7750-2438-40c9-8838-8561fceb277c
-- title:
--   Lemma 7.5 (Skeleton nodes)
-- statement:
--   Fix the cycle before sampling. Let $0<\alpha\le n$ and sample each vertex independently with probability $\alpha/n$. The positive coefficient in the lower hop threshold and the requested failure exponent are fixed before the graph.
--
--   Assume the cycle has $h$ edges with
--
--   $$
--   h\in\Omega((n\log^2 n)/\alpha).
--   $$
--
--   With high probability the following hold jointly, for $S$ the sampled set and $R=S\cap V(C)$:
--
--   1. $|R|\ge2$.
--   2. Every $R$-segment has at most $O((n/\alpha)\log n)$ edges.
--   3. $|S|\in\Theta(\alpha)$.
--
--   The implementation of the last conclusion uses $\alpha/2\le |S|\le2\alpha$. The segment constant and a size threshold can be chosen before the graph and $\alpha$ for any fixed positive lower-hop coefficient and requested confidence.
--
--   Differences from the source:
--   - encoding: asymptotic O, Omega and high-probability notation → positive constants and a size threshold quantified before the network and varying algorithm parameters; reason: this spells out the uniform asymptotic statement, retaining arbitrary real parameters and fixed polynomial confidence
--   - generalization: a fixed cycle in an input network → a fixed simple cycle in any finite undirected weighted graph, including disconnected graphs; reason: the sampling conclusion depends only on the fixed cycle and its vertex count
--   - encoding: sample size Theta(alpha) and segment length O((n/alpha) log n) → sample size between alpha/2 and 2 alpha and a uniformly quantified segment coefficient; reason: the source Chernoff-bound argument permits these fixed relative errors for sufficiently large n
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf, Lemma 7.5, printed p. 36 / PDF p. 38.

import Definitions.Def_DistributedMWC440_UpperBound_Operations

open scoped ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section

namespace DistributedMWC440.UpperBound

theorem lemma_7_5 (cHop confidence : ℝ) (hc : 0 < cHop) (hconf : 0 < confidence) :
    ∃ (n₀ : ℕ) (cseg : ℝ), 0 < cseg ∧
    ∀ n ≥ max 3 n₀, ∀ (W : WGraph (Fin n)) (C : Cycle W),
    ∀ α : ℝ, 0 < α → α ≤ n →
      cHop * (n * (Real.log n)^2 / α) ≤ C.walk.length →
      ENNReal.ofReal (1-(n : ℝ)^(-confidence)) ≤
        samplingLaw α {σ | GoodSample C (sampled σ) α cseg} := by sorry

end DistributedMWC440.UpperBound
