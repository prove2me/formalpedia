-- Prove2me | Theorems.Thm_DynStochMatching_Reward_lemma_9
-- name    : DynStochMatching.Reward.lemma_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T20:43:14.391517+00:00
-- url     : https://prove2.me/theorems/3b9157b0-ae25-4765-a600-8c377c814176
-- title:
--   Lemma 9 — Polynomial QCLP flow construction
-- statement:
--   There is a uniform polynomial arithmetic algorithm, using one polynomial-size exact LP call, computing the B.2 feasible QB flow. Its reward is at least one quarter of the optimal online reward on arbitrary graphs, one half on bipartite graphs, and the whole optimal reward in the bipartite-asymmetric setting. QB has an attained optimum Q*. The printed final clauses are retained literally: r* ≤ Q*/4 on arbitrary graphs, r* ≤ Q*/2 on bipartite graphs, and r* ≤ Q* in the asymmetric setting. The first two printed conclusions are not silently corrected; see finding I1.
--
--   Source statement:
--
--   There is a polynomial-time algorithm that computes a feasible flow $\tilde x$ for problem $(QB)$ such that $\sum_{(i,j)\in\mathcal T^2}r(i,j)\cdot\tilde x_{i,j}\ge\kappa\cdot r^{\pi^*}$, where $\kappa=\frac14$ on arbitrary graphs, $\kappa=\frac12$ on bipartite graphs, and $\kappa=1$ in the bipartite-asymmetric setting. In particular, we have $r^{\pi^*}\le\kappa\cdot Q^*$ in these settings.
--
--   Differences from the source:
--   - generalization: a finite collection of arriving types → Fin n also permits the empty type graph; reason: the empty instance has zero rewards, flows and costs; restricting to nonempty graphs recovers every source instance
--   - encoding: independently marked Poisson arrivals and randomized adapted policies → a canonical product of independent exponential seeds, inverse CDF marks and pair stopping times up to null events; reason: this realizes the same laws and observable information; null modifications remove impossible seed paths without revealing future arrivals or sojourns
--   - encoding: the optimal online policy value r* or c* → supremum or infimum over all feasible observable policies in complete extended orders; reason: no optimum is supplied as an input; explicit attainment clauses retain the source optimum convention where used
--   - encoding: polynomial-time computation → uniform exact arithmetic/comparison register programs relative to one polynomial-size exact LP call and exact samples; reason: this makes the operational convention explicit for full real input and does not assert bit complexity or strongly polynomial LP solving
--   - encoding: infinite abandonment-rate shorthand on the immediate side → a separate immediate lifetime constructor and zero outgoing active flow; reason: immediate vertices are available for their arrival decision and no infinite real product is evaluated
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, Lemma 9, printed p. 22 / PDF p. 23

import Definitions.Def_DynStochMatching_Reward_Algorithm

open MeasureTheory Filter
open scoped ENNReal Classical

namespace DynStochMatching.Reward

theorem lemma_9 : polynomialFlowConstruction ∧
    ∀ (n : ℕ) (D : Instance n) (O : LinearOracle), sourceDomain D →
      (∃ x, qbFeasible D x ∧ (flowReward D x : EReal) = qbValue D) ∧
      qbFeasible D (chosenFlow O D) ∧ flowGuarantees D (chosenFlow O D) ∧
      optimalReward D ≤ (1 / 4 : ℝ) * qbValue D ∧
      ((∃ side, IsBipartition D side) → optimalReward D ≤ (1 / 2 : ℝ) * qbValue D) ∧
      ((∃ side, IsAsymmetric D side) → optimalReward D ≤ qbValue D) := by sorry

end DynStochMatching.Reward
