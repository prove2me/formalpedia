-- Prove2me | Theorems.Thm_CompetitivePaging_LowerBound_expCost_append_ge_uncoveredProb
-- name    : CompetitivePaging.LowerBound.expCost_append_ge_uncoveredProb
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:18:53.106739+00:00
-- url     : https://prove2.me/theorems/7a601de9-fdf9-482a-9c42-e6c1d06dae4a
-- title:
--   Requesting vertex $i$ costs a randomized algorithm at least $p_i$ in expectation
-- statement:
--   Let $M$ be a uniform metric space: any two distinct points are at distance $1$. Let $A$ be a randomized on-line $k$-server algorithm on $M$ (a probability space of coin outcomes and a deterministic on-line algorithm for each outcome), let $\sigma$ be a request sequence, and let $i\in M$ be a vertex such that the event "$i$ is not covered after $\sigma$" is measurable. Write $C_A(\sigma)$ for the expected cost of $A$ on $\sigma$ and $p_i$ for the probability that $i$ is not covered after $\sigma$. Then
--
--   $$
--   C_A(\sigma\, i) \;\ge\; C_A(\sigma) + p_i ,
--   $$
--
--   where $\sigma\, i$ is $\sigma$ followed by one request to $i$.
--
--   This is the link between the adversary's probability vector and the cost of the on-line algorithm: every request to a vertex $i$ adds at least $p_i$ to $A$'s expected cost.
--
--   **Formalization Note** The paper states that the expected cost of the request "is $p_i$"; that is exact for an algorithm that moves one server only when the requested vertex is uncovered. For an arbitrary algorithm, extra movements only add cost, so the statement is the inequality. Expected costs are values in $[0,\infty]$ (lower Lebesgue integrals), as in the published `KServer_randomized` definitions.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 7, §5, proof of Theorem 4 ("If the nemesis sequence requests a vertex i, then the expected cost incurred by A is p_i.")

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized
import Definitions.Def_CompetitivePaging_LowerBound_uncoveredProb

namespace CompetitivePaging.LowerBound

theorem expCost_append_ge_uncoveredProb {k : ℕ} (M : Type) [MetricSpace M]
    (hd : ∀ x y : M, x ≠ y → dist x y = 1) (A : KServer.RandomizedAlgorithm k M)
    (σ : List M) (i : M)
    (hmeas : @MeasurableSet A.ι A.ms {ω | i ∉ Set.range ((A.alg ω).conf σ)}) :
    A.expCost σ + ENNReal.ofReal (uncoveredProb A σ i) ≤ A.expCost (σ ++ [i]) := by sorry

end CompetitivePaging.LowerBound
