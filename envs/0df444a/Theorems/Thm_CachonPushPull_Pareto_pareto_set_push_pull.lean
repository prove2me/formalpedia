-- Prove2me | Theorems.Thm_CachonPushPull_Pareto_pareto_set_push_pull
-- name    : CachonPushPull.Pareto.pareto_set_push_pull
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:30:47.527984+00:00
-- url     : https://prove2.me/theorems/6f672bc6-1820-4c2d-a094-2b92eaf55bbb
-- title:
--   Theorem 6: the Pareto set of push and pull contracts is exactly $q \in [q^P, q^o]$ in both modes, and those pull contracts survive the push challenge
-- statement:
--   Let demand have distribution function $F$ with $F(0) = 0$, strictly increasing on $[0, \infty)$, with a density $f$ on $(0, \infty)$ and a strictly increasing generalized failure rate. Let $v < c < p$ be the salvage value, production cost and retail price, and let $q^o$ be the chain-optimal quantity, $F(q^o) = (p - c)/(p - v)$.
--
--   Consider the single wholesale price contracts: a push contract with quantity $q$ has payoffs $(\hat\pi_r(q), \hat\pi_s(q))$ (retailer, supplier), a pull contract with quantity $q$ has payoffs $(\pi_r(q), \pi_s(q))$, and a contract is admissible when $q \ge 0$ and its wholesale price lies in $[c, p]$. Then there is a quantity $q^P$ with $0 < q^P < q^o$ such that
--
--   1. each firm earns the same under the pull and the push contract with quantity $q^P$: $\pi_r(q^P) = \hat\pi_r(q^P)$ and $\pi_s(q^P) = \hat\pi_s(q^P)$, and $q^P$ is the only $q > 0$ with $\pi_r(q) = \hat\pi_r(q)$;
--   2. the Pareto set among the admissible push and pull contracts is exactly
--   $$
--   \{\text{push}, \text{pull}\} \times [q^P, q^o] ;
--   $$
--   3. every pull contract with $q \in [q^P, q^o]$ survives the push challenge, i.e. the retailer strictly prefers not to prebook.
--
--   This is the main result of §4: when both push and pull contracts are available, the Pareto set contains contracts of both types, neither the supplier's preferred push contract $\hat q^*$ nor the retailer's preferred pull contract $q^*$ is in it, and its minimum efficiency $\Pi(q^P)/\Pi^o$ exceeds that of either type alone.
--
--   **Formalization Note** The paper states that the Pareto set "includes all" these contracts; its proof shows also that no other contract is Pareto, so the statement is the set equality. The admissibility window $c \le w \le p$ (equivalently $0 \le q \le q^o$ in both modes) is an explicit reading added by the formalization: on the unrestricted space $q \ge 0$ pull contracts with $q > q^o$ are Pareto (the supplier earns more than $\Pi^o$ there and the retailer a loss), and the theorem would be false. Survival of the push challenge (Lemma 5) is included because the proof's last sentence relies on it: without it the nominal pull payoffs would not be the payoffs actually earned.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 231, Theorem 6 (with Lemma 4, p. 230, and Lemma 5, p. 231)

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Contracts

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Theorem 6, p. 231, with Lemma 5: the Pareto set among the admissible push and pull contracts
is exactly the push and pull contracts with `q ∈ [q^P, q^o]`, where `q^P ∈ (0, q^o)` is the unique
positive quantity at which each firm earns the same with the pull and the push contract; and all
those pull contracts survive the push challenge. -/
theorem pareto_set_push_pull (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo : cdf μ qo = (p - c) / (p - v)) :
    ∃ qP : ℝ, 0 < qP ∧ qP < qo ∧
      pullRetailerProfit μ p c v qP = pushRetailerProfit μ p v qP ∧
      pullSupplierProfit μ c v qP = pushSupplierProfit μ p c v qP ∧
      (∀ q : ℝ, 0 < q → pullRetailerProfit μ p c v q = pushRetailerProfit μ p v q → q = qP) ∧
      paretoSet μ p c v = {k : Contract | k.q ∈ Set.Icc qP qo} ∧
      ∀ q ∈ Set.Icc qP qo, SurvivesPushChallenge μ p c v q := by sorry

end CachonPushPull.Pareto
