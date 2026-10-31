-- Prove2me | Theorems.Thm_DynStochMatching_Reward_claim_3
-- name    : DynStochMatching.Reward.claim_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T20:43:46.35899+00:00
-- url     : https://prove2.me/theorems/6e5304cd-8032-4c0f-997c-2801a839bd25
-- title:
--   Claim 3 — Reward LP upper bound
-- statement:
--   For every ordinary or bipartite-asymmetric instance, the RB optimum is attained and upper-bounds the optimal online liminf average reward over all admissible observable policies.
--
--   Source statement:
--
--   $U^*\ge r^{\pi^*}$.
--
--   Differences from the source:
--   - generalization: a finite collection of arriving types → Fin n also permits the empty type graph; reason: the empty instance has zero rewards, flows and costs; restricting to nonempty graphs recovers every source instance
--   - encoding: independently marked Poisson arrivals and randomized adapted policies → a canonical product of independent exponential seeds, inverse CDF marks and pair stopping times up to null events; reason: this realizes the same laws and observable information; null modifications remove impossible seed paths without revealing future arrivals or sojourns
--   - encoding: the optimal online policy value r* or c* → supremum or infimum over all feasible observable policies in complete extended orders; reason: no optimum is supplied as an input; explicit attainment clauses retain the source optimum convention where used
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, Claim 3, printed p. 21 / PDF p. 22

import Definitions.Def_DynStochMatching_Reward_Algorithm

open MeasureTheory Filter
open scoped ENNReal Classical

namespace DynStochMatching.Reward

theorem claim_3 {n : ℕ} (D : Instance n) (hsource : sourceDomain D) :
    (∃ x, rbFeasible D x ∧ (flowReward D x : EReal) = rbValue D) ∧
    rbValue D ≥ optimalReward D := by sorry

end DynStochMatching.Reward
