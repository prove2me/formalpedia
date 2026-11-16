-- Prove2me | Theorems.Thm_BatchMaxService_Metric_Supplement_hidden_request_lower_bounds
-- name    : BatchMaxService.Metric.Supplement.hidden_request_lower_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:11:59.324332+00:00
-- url     : https://prove2.me/theorems/a39b1dcf-530f-4bed-a850-d3f60a098f2a
-- title:
--   Theorem 7.7 — One hidden request: line and star deterministic/randomized lower bounds
-- statement:
--   Suppose the policy knows in advance that exactly one hidden request arrives at time zero and none arrive later. Under each of elective and automatic service, both conclusions hold:
--
--   1. On the line $\{-1,0,1\}$ with start $0$, every feasible deterministic policy has a fixed request site of cost at least $3$, and every almost-surely feasible randomized policy has a fixed seed-independent request site of expected cost at least $2$.
--   2. On the unit star with $d\ge1$ leaves and center start, the respective fixed-leaf lower bounds are $2d-1$ and $d$.
--
--   $$\operatorname{OPT}(I_v)=1,\qquad \operatorname{ALG}_A(I_v)\ge2d-1,\qquad \mathbb E_\omega[\operatorname{ALG}_{A_\omega}(I_v)]\ge d.$$
--
--   The deterministic and randomized witnesses may differ. The line constants are stated separately as well as covered by the two-leaf star. Randomization ranges over arbitrary probability spaces with measurable extended nonnegative cost and almost-sure service for each promised input; infinite expected costs are included. Waiting and revisits are unrestricted. There is no additive constant. The zero-leaf representation retains the trivial one-site promised input with offline value zero and a concrete feasible zero-cost parked policy.
--
--   Differences from the source:
--   - encoding: three-site line and unit stars, both service rules, and exactly one promised time-zero hidden request → literal three-site absolute-distance metric and d+1 indexed star sites, with one fixed announced identity and leaf-independent arrival data; reason: indexing and fixed labels change no search problem; the one-site zero-leaf convention is explicitly retained
--   - encoding: randomized feasible algorithms against an oblivious adversary and their expected costs → arbitrary probability-space mixtures of feedback policies, almost-sure feasibility on each fixed promised input, measurable ENNReal costs and a hidden-leaf witness outside the lintegral; reason: this retains every measurable randomized policy, permits infinite expectation and fixes the input independently of the random seed
-- source:
--   Lu, Ren, Liu, Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), canonical source.pdf sha256 652f1a7bbf08e31c9fd0855a098b7b7439589f55b2df3115db7c34adc0eaec34, Theorem 7.7, printed p. 29 / PDF p. 30

import Mathlib
import Definitions.Def_BatchMaxService_Metric_Supplement_LowerBounds

namespace BatchMaxService.Metric.Supplement

theorem hidden_request_lower_bounds :
    (∀ [MetricSpace (Fin 3)], ThreeSiteLineMetric →
      ∀ r : Rule, HiddenSearchBounds (n := 3) r 1 {0, 2} 3 2) ∧
    (∀ d : ℕ, ∀ [MetricSpace (Fin (d + 1))], UnitStarMetric d →
      ∀ r : Rule,
        (d = 0 →
          ruleOPT r (singleRequest (0 : Fin (d + 1)) 0) = 0 ∧
          ValidOn .blind r (parkedPolicy (d + 1)) (singleRequest 0 0) ∧
          policyCost .blind r (parkedPolicy (d + 1)) (singleRequest 0 0) = 0) ∧
        (1 ≤ d → HiddenSearchBounds (n := d + 1) r 0 (starLeaves d) (2 * (d : ℝ) - 1) d)) := by sorry

end BatchMaxService.Metric.Supplement
