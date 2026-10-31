-- Prove2me | Theorems.Thm_DynStochMatching_Reward_claim_1
-- name    : DynStochMatching.Reward.claim_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T20:40:41.677839+00:00
-- url     : https://prove2.me/theorems/50577f94-c849-4630-8447-1d77d895560e
-- title:
--   Claim 1 — Modified match counts
-- statement:
--   Fix an ordinary instance, extended nonnegative costs, an admissible optimal deterministic stationary policy, and two types i,j. Let A_t count actual earlier-i/later-j matches, let ζ_q be the ordered exogenous epochs, and let ĤA_q count eventual matches with both endpoints arrived by ζ_q. The deterministic-time expected rate converges to x*; the expectation of ĤA_q, divided by the random ζ_q, converges almost surely to the same x*. No random-time convergence is assumed.
--
--   Source statement:
--
--   For every $(i,j)\in\mathcal T^2$, $\lim_{q\to+\infty}\frac{1}{\zeta_q}\cdot\mathbb E[\hat A_q(i,j)]=x^*_{i,j}$ almost surely.
--
--   Differences from the source:
--   - generalization: a finite collection of arriving types → Fin n also permits the empty type graph; reason: the empty instance has zero rewards, flows and costs; restricting to nonempty graphs recovers every source instance
--   - encoding: independently marked Poisson arrivals and randomized adapted policies → a canonical product of independent exponential seeds, inverse CDF marks and pair stopping times up to null events; reason: this realizes the same laws and observable information; null modifications remove impossible seed paths without revealing future arrivals or sojourns
--   - generalization: stationary decisions on type-count realization states → fixed decisions on the ordered list of available types; reason: count-state rules are included; permitting relative arrival order adds stationary policies without restricting the source rules
--   - encoding: agent indices start at 1 and x* is defined as a limit → agent indices start at 0 and deterministic-time convergence is included explicitly; reason: index translation changes no matches and the convergence conclusion avoids a default value for a nonexistent limit
--   - generalization: finite nonnegative abandonment penalties → extended nonnegative abandonment penalties; reason: the stationary count-rate conclusion does not depend on finiteness of these penalties; finite penalties recover the source
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, Claim 1, printed p. 12 / PDF p. 13

import Definitions.Def_DynStochMatching_Reward_Counts

open MeasureTheory Filter
open scoped ENNReal Classical

namespace DynStochMatching.Reward

theorem claim_1 {n : ℕ} (D : Instance n) (C : Costs n) (π : MatchingPolicy)
    (hordinary : IsOrdinary D) (hpolicy : admissible D π) (hstationary : stationary D π)
    (hoptimal : averageCost D C π = optimalCost D C) (i j : Fin n) :
    Tendsto (fun t : ℝ => expectedMatchCount D π i j t / t) atTop
      (nhds (rateOfMatches D π i j)) ∧
    (∀ᵐ ω ∂seedLaw, Tendsto
      (fun q : ℕ => expectedModifiedCount D π i j q / (epoch D ω q).toReal)
      atTop (nhds (rateOfMatches D π i j))) := by sorry

end DynStochMatching.Reward
