-- Prove2me | Theorems.Thm_DynStochMatching_Reward_theorem_2
-- name    : DynStochMatching.Reward.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T20:43:17.771282+00:00
-- url     : https://prove2.me/theorems/ad207695-7f0c-4f95-9e49-52bbcac5e9ae
-- title:
--   Theorem 2 — Polynomial-time reward approximation in all three regimes
-- statement:
--   There are uniform finite offline and online arithmetic/comparison programs implementing the randomized compatibility policy, with polynomial work in the finite type input and the current realization size, one polynomial-size offline LP call and two exact independent uniform samples per arrival. For every source instance and every correct exact LP oracle, the resulting concrete policy is admissible and earns at least (e−1)/(4e) of the optimal online average reward, at least (e−1)/(2e) when the nonzero-reward graph is bipartite, and at least 1−1/e in the bipartite-asymmetric setting. An optimal deterministic stationary policy attaining the benchmark is also asserted to exist. No bounded population, finite horizon, common abandonment rate or reward sign assumption is imposed.
--
--   Source statement:
--
--   There exists a polynomial-time constant-factor approximation for the reward-maximization dynamic stochastic matching problem.
--   • On arbitrary graphs, our algorithm computes a $(\frac{e-1}{4e})$-approximate matching policy.
--   • On bipartite graphs, our algorithm computes a $(\frac{e-1}{2e})$-approximate matching policy.
--   • In the bipartite-asymmetric setting, our algorithm computes a $(1-\frac1e)$-approximate policy.
--
--   Differences from the source:
--   - generalization: a finite collection of arriving types → Fin n also permits the empty type graph; reason: the empty instance has zero rewards, flows and costs; restricting to nonempty graphs recovers every source instance
--   - encoding: independently marked Poisson arrivals and randomized adapted policies → a canonical product of independent exponential seeds, inverse CDF marks and pair stopping times up to null events; reason: this realizes the same laws and observable information; null modifications remove impossible seed paths without revealing future arrivals or sojourns
--   - encoding: the optimal online policy value r* or c* → supremum or infimum over all feasible observable policies in complete extended orders; reason: no optimum is supplied as an input; explicit attainment clauses retain the source optimum convention where used
--   - encoding: polynomial-time computation → uniform exact arithmetic/comparison register programs relative to one polynomial-size exact LP call and exact samples; reason: this makes the operational convention explicit for full real input and does not assert bit complexity or strongly polynomial LP solving
--   - encoding: unspecified tie rules and empty conditional-label cases → fixed type/label/identity ties and an isolated never-match label when the active support or mass is zero; reason: tie choices are allowed by the source and the isolated branch completes undefined empty distributions without adding matches
--   - encoding: infinite abandonment-rate shorthand on the immediate side → a separate immediate lifetime constructor and zero outgoing active flow; reason: immediate vertices are available for their arrival decision and no infinite real product is evaluated
--   - reading: Algorithm 2 on PDF 46 omits the reward coefficient in its preliminary flow inequality → the preliminary flow satisfies the reward-weighted guarantee of Lemma 9; reason: the step explicitly cites Lemma 9, and the B.3 preamble requires its performance bound; this resolves the missing coefficient (I5)
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, Theorem 2, printed p. 21 / PDF p. 22

import Definitions.Def_DynStochMatching_Reward_Algorithm
import Definitions.Def_DynStochMatching_Reward_Counts

open MeasureTheory Filter
open scoped ENNReal Classical

namespace DynStochMatching.Reward

theorem theorem_2 : polynomialPolicyImplementation ∧
    ∀ (n : ℕ) (D : Instance n) (O : LinearOracle), sourceDomain D →
      (∃ π : MatchingPolicy, admissible D π ∧ stationary D π ∧ averageReward D π = optimalReward D) ∧
      admissible D (algorithmPolicy O D) ∧
      averageReward D (algorithmPolicy O D) ≥
        ((Real.exp 1 - 1) / (4 * Real.exp 1) : ℝ) * optimalReward D ∧
      ((∃ side, IsBipartition D side) → averageReward D (algorithmPolicy O D) ≥
        ((Real.exp 1 - 1) / (2 * Real.exp 1) : ℝ) * optimalReward D) ∧
      ((∃ side, IsAsymmetric D side) → averageReward D (algorithmPolicy O D) ≥
        (1 - 1 / Real.exp 1 : ℝ) * optimalReward D) := by sorry

end DynStochMatching.Reward
