-- Prove2me | Theorems.Thm_DynStochMatching_Reward_lemma_1
-- name    : DynStochMatching.Reward.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T20:40:21.945217+00:00
-- url     : https://prove2.me/theorems/522618eb-60fa-4298-8815-5d86c3682b63
-- title:
--   Lemma 1 — Cost LP lower bound
-- statement:
--   For every ordinary instance and symmetric nonnegative, possibly infinite edge costs and abandonment penalties, the CB optimum is attained and is no larger than the optimal online average cost over all feasible observable policies. Infinite forbidden costs are retained.
--
--   Source statement:
--
--   $L^*\le c^{\pi^*}$.
--
--   Differences from the source:
--   - generalization: a finite collection of arriving types → Fin n also permits the empty type graph; reason: the empty instance has zero rewards, flows and costs; restricting to nonempty graphs recovers every source instance
--   - encoding: independently marked Poisson arrivals and randomized adapted policies → a canonical product of independent exponential seeds, inverse CDF marks and pair stopping times up to null events; reason: this realizes the same laws and observable information; null modifications remove impossible seed paths without revealing future arrivals or sojourns
--   - encoding: the optimal online policy value r* or c* → supremum or infimum over all feasible observable policies in complete extended orders; reason: no optimum is supplied as an input; explicit attainment clauses retain the source optimum convention where used
--   - generalization: nonnegative abandonment penalties → extended nonnegative penalties, including infinity; reason: finite penalties specialize to the source and extended costs remain in a complete nonnegative order
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, Lemma 1, printed p. 11 / PDF p. 12

import Definitions.Def_DynStochMatching_Reward_Flows

open MeasureTheory Filter
open scoped ENNReal Classical

namespace DynStochMatching.Reward

theorem lemma_1 {n : ℕ} (D : Instance n) (C : Costs n) (hordinary : IsOrdinary D) :
    (∃ x, rbFeasible D x ∧ flowCost C x = cbValue D C) ∧
    cbValue D C ≤ optimalCost D C := by sorry

end DynStochMatching.Reward
