-- Prove2me | Theorems.Thm_CompetitivePaging_LowerBound_uncoveredProb_sum_eq_one
-- name    : CompetitivePaging.LowerBound.uncoveredProb_sum_eq_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:18:23.747177+00:00
-- url     : https://prove2.me/theorems/af5be42f-ab90-472a-8f5f-243ca6a55b75
-- title:
--   With $n-1$ servers on distinct vertices, $\sum_i p_i = 1$
-- statement:
--   Let $M$ be a finite set of $n\ge 2$ vertices with a metric, and let $A$ be a randomized on-line algorithm with $n-1$ servers on $M$, given by a probability space $(\Omega,\mu)$ of coin outcomes and a deterministic on-line algorithm $A_\omega$ for each outcome. Fix a request sequence $\sigma$ and suppose that, for every outcome $\omega$, the $n-1$ servers of $A_\omega$ occupy pairwise distinct vertices after serving $\sigma$, and that for each vertex $i$ the event "$i$ is not covered after $\sigma$" is measurable. Let $p_i$ be the probability of that event. Then
--
--   $$
--   \sum_{i\in M} p_i = 1 .
--   $$
--
--   Exactly one vertex is uncovered in every outcome, so the uncovered probabilities form a probability distribution on the vertices; the adversary's argument in the lower bound is carried out on this distribution.
--
--   **Formalization Note** The platform's configuration model allows two servers on the same vertex; the paper's identity holds when the servers are on distinct vertices (the setting of the paper, where an algorithm never needs to stack servers), so injectivity of each drawn configuration after $\sigma$ is a hypothesis. Measurability of the uncovered events is the standing convention that $p_i$ is a probability.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 7, §5, proof of Theorem 4 ("Note that Σ_i p_i = 1.")

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized
import Definitions.Def_CompetitivePaging_LowerBound_uncoveredProb

namespace CompetitivePaging.LowerBound

theorem uncoveredProb_sum_eq_one (n : ℕ) (hn : 2 ≤ n) (M : Type) [MetricSpace M] [Fintype M]
    (hM : Fintype.card M = n) (A : KServer.RandomizedAlgorithm (n - 1) M) (σ : List M)
    (hinj : ∀ ω, Function.Injective ((A.alg ω).conf σ))
    (hmeas : ∀ i : M, @MeasurableSet A.ι A.ms {ω | i ∉ Set.range ((A.alg ω).conf σ)}) :
    ∑ i, uncoveredProb A σ i = 1 := by sorry

end CompetitivePaging.LowerBound
