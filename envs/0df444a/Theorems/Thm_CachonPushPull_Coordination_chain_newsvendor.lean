-- Prove2me | Theorems.Thm_CachonPushPull_Coordination_chain_newsvendor
-- name    : CachonPushPull.Coordination.chain_newsvendor
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:32:34.616805+00:00
-- url     : https://prove2.me/theorems/bfff040b-1bc2-4e37-b141-421f026d04d0
-- title:
--   Eq. (2) — the chain profit $\Pi$ is concave and maximized at $q^o$ with $F(q^o) = (p-c)/(p-v)$
-- statement:
--   Let demand satisfy the standing assumptions ($F(0) = 0$, $F$ strictly increasing on $[0,\infty)$ with a density on $(0,\infty)$, IGFR) and let $v < c < p$. Let $\Pi(q) = (p - v)S(q) - (c - v)q$ be the integrated supply chain's expected profit. Then:
--
--   1. there is $q^o > 0$ with
--   $$
--   F(q^o) = \frac{p - c}{p - v};
--   $$
--   2. $\Pi$ is concave on $[0, \infty)$;
--   3. every $q^o$ with $F(q^o) = (p-c)/(p-v)$ is positive, maximizes $\Pi$ over $[0, \infty)$, and $\Pi$ is strictly increasing on $[0, q^o]$;
--   4. every maximizer $q \ge 0$ of $\Pi$ over $[0, \infty)$ satisfies $F(q) = (p-c)/(p-v)$.
--
--   This is the newsvendor benchmark: $\Pi^o = \Pi(q^o)$ is the largest expected profit the supply chain can earn, and efficiency is measured against it.
--
--   **Formalization Note** The paper writes "increasing for $q \in [0, q^o]$"; the statement takes the strict reading, which holds because $\Pi'(q) = (p-v)(1 - F(q)) - (c - v) > 0$ for $q < q^o$. The existence of $q^o$ is part of the statement, so that theorems taking $q^o$ as a parameter are not vacuous.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 227, Section 4.1, Eq. (2)

import Mathlib
import Definitions.Def_CachonPushPull_Coordination_Game

namespace CachonPushPull.Coordination

open MeasureTheory ProbabilityTheory

/-- Eq. (2), p. 227: the integrated supply chain faces a newsvendor problem. A quantity `q^o` with
`F(q^o) = (p - c)/(p - v)` exists; `Π` is concave on `[0, ∞)`; every such `q^o` is positive,
maximizes `Π` over `[0, ∞)`, and `Π` is (strictly) increasing on `[0, q^o]`; and every maximizer of
`Π` over `[0, ∞)` satisfies the fractile equation. -/
theorem chain_newsvendor (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    (∃ qo : ℝ, 0 < qo ∧ cdf μ qo = (p - c) / (p - v)) ∧
    ConcaveOn ℝ (Set.Ici 0) (chainProfit μ p c v) ∧
    (∀ qo : ℝ, cdf μ qo = (p - c) / (p - v) →
      0 < qo ∧ IsMaxOn (chainProfit μ p c v) (Set.Ici 0) qo ∧
        StrictMonoOn (chainProfit μ p c v) (Set.Icc 0 qo)) ∧
    ∀ q : ℝ, 0 ≤ q → IsMaxOn (chainProfit μ p c v) (Set.Ici 0) q →
      cdf μ q = (p - c) / (p - v) := by sorry

end CachonPushPull.Coordination
