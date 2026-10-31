-- Prove2me | Theorems.Thm_DynStochMatching_Reward_lemma_10
-- name    : DynStochMatching.Reward.lemma_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T20:43:46.140458+00:00
-- url     : https://prove2.me/theorems/e58c68e2-5a61-497b-962b-186aab3c782f
-- title:
--   Lemma 10 — All three policy reward guarantees
-- statement:
--   For every ordinary or bipartite-asymmetric instance and every QB-feasible flow satisfying the applicable B.3 performance bounds, the randomized compatibility policy executed from that flow has average reward at least (e−1)/(4e) times the optimal online reward; on bipartite graphs the factor is (e−1)/(2e), and in the bipartite-impatient/asymmetric setting it is (e−1)/e. The policy uses the actual conditional labels and chronological greedy decisions, including explicit empty-support branches.
--
--   Source statement:
--
--   For all instances of the dynamic stochastic matching problem, we have $r^{\hat\pi}\ge(\frac{e-1}{4e})\cdot r^{\pi^*}$. On bipartite graphs, we have $r^{\hat\pi}\ge(\frac{e-1}{2e})\cdot r^{\pi^*}$, while $r^{\hat\pi}\ge(\frac{e-1}{e})\cdot r^{\pi^*}$ in the bipartite-impatient setting.
--
--   Differences from the source:
--   - generalization: a finite collection of arriving types → Fin n also permits the empty type graph; reason: the empty instance has zero rewards, flows and costs; restricting to nonempty graphs recovers every source instance
--   - encoding: independently marked Poisson arrivals and randomized adapted policies → a canonical product of independent exponential seeds, inverse CDF marks and pair stopping times up to null events; reason: this realizes the same laws and observable information; null modifications remove impossible seed paths without revealing future arrivals or sojourns
--   - encoding: the optimal online policy value r* or c* → supremum or infimum over all feasible observable policies in complete extended orders; reason: no optimum is supplied as an input; explicit attainment clauses retain the source optimum convention where used
--   - encoding: unspecified tie rules and empty conditional-label cases → fixed type/label/identity ties and an isolated never-match label when the active support or mass is zero; reason: tie choices are allowed by the source and the isolated branch completes undefined empty distributions without adding matches
--   - encoding: infinite abandonment-rate shorthand on the immediate side → a separate immediate lifetime constructor and zero outgoing active flow; reason: immediate vertices are available for their arrival decision and no infinite real product is evaluated
--   - reading: Algorithm 2 on PDF 46 omits the reward coefficient in its preliminary flow inequality → the preliminary flow satisfies the reward-weighted guarantee of Lemma 9; reason: the step explicitly cites Lemma 9, and the B.3 preamble requires its performance bound; this resolves the missing coefficient (I5)
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, Lemma 10, printed p. 45 / PDF p. 46

import Definitions.Def_DynStochMatching_Reward_Algorithm

open MeasureTheory Filter
open scoped ENNReal Classical

namespace DynStochMatching.Reward

theorem lemma_10 {n : ℕ} (D : Instance n) (x : Flow n) (hsource : sourceDomain D)
    (hfeasible : qbFeasible D x) (hperformance : flowGuarantees D x) :
    averageReward D (compatibilityPolicy D x) ≥
      ((Real.exp 1 - 1) / (4 * Real.exp 1) : ℝ) * optimalReward D ∧
    ((∃ side, IsBipartition D side) → averageReward D (compatibilityPolicy D x) ≥
      ((Real.exp 1 - 1) / (2 * Real.exp 1) : ℝ) * optimalReward D) ∧
    ((∃ side, IsAsymmetric D side) → averageReward D (compatibilityPolicy D x) ≥
      ((Real.exp 1 - 1) / Real.exp 1 : ℝ) * optimalReward D) := by sorry

end DynStochMatching.Reward
