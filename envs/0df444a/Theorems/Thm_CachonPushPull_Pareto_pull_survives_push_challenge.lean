-- Prove2me | Theorems.Thm_CachonPushPull_Pareto_pull_survives_push_challenge
-- name    : CachonPushPull.Pareto.pull_survives_push_challenge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:30:00.854988+00:00
-- url     : https://prove2.me/theorems/e2d403db-1c96-463b-b7b6-5b5424586a42
-- title:
--   Lemma 5: all pull contracts with $q \ge q^P$ survive the push challenge
-- statement:
--   Let demand satisfy the standing assumptions, $v < c < p$, and let $q^P > 0$ satisfy $\pi_r(q^P) = \hat\pi_r(q^P)$ (by Lemma 4 there is exactly one such quantity). For every $q \ge q^P$, consider the pull contract with single wholesale price $w_1 = w_2 = w_1(q)$. Then
--
--   1. if the retailer prebooks nothing, the supplier's optimal production is exactly $q$ (and no other quantity);
--   2. the retailer's profit in that case is the nominal pull profit, $\pi_r(0, q) = \pi_r(q)$;
--   3. the contract survives the push challenge: every prebook $y > 0$, followed by an optimal supplier reply, gives the retailer strictly less expected profit than prebooking zero.
--
--   Hence on $q \ge q^P$ a pull contract is really played as pull, and the nominal payoffs $(\pi_r(q), \pi_s(q))$ used in Theorem 6 are the firms' actual payoffs.
--
--   **Formalization Note** The paper's "the retailer prefers to prebook zero inventory … rather than to prebook any positive amount" is read as strict preference; its proof shows the retailer's profit strictly decreases in the prebook. The statement covers every $q \ge q^P$, including $q > q^o$, as the paper's does.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 231, Lemma 5 (with p. 233, Eqs. (20)-(21))

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Lemma 5, p. 231: all pull contracts with `q ≥ q^P` survive the push challenge. With no
prebook the supplier produces exactly `q`, so the retailer earns the nominal pull profit `π_r(q)`. -/
theorem pull_survives_push_challenge (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qP : ℝ) (hqP : 0 < qP) (hqP_eq : pullRetailerProfit μ p c v qP = pushRetailerProfit μ p v qP) :
    ∀ q : ℝ, qP ≤ q →
      (∀ Q₀ : ℝ, IsSupplierBestReply μ c v (pullPrice μ c v q) (pullPrice μ c v q) 0 Q₀ ↔ Q₀ = q) ∧
      apdRetailerProfit μ p v (pullPrice μ c v q) (pullPrice μ c v q) 0 q =
        pullRetailerProfit μ p c v q ∧
      SurvivesPushChallenge μ p c v q := by sorry

end CachonPushPull.Pareto
