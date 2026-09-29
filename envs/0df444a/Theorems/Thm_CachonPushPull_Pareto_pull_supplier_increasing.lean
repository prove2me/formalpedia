-- Prove2me | Theorems.Thm_CachonPushPull_Pareto_pull_supplier_increasing
-- name    : CachonPushPull.Pareto.pull_supplier_increasing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:26:52.964249+00:00
-- url     : https://prove2.me/theorems/5e9f5049-a446-42bd-a043-49891bbb010b
-- title:
--   Eq. (9): the pull supplier's profit is increasing, $\pi_s'(q) = (p-v)(1-F(q^o))j(q)h(q)$
-- statement:
--   Let demand satisfy the standing assumptions, $v < c < p$, and let $q^o$ satisfy $F(q^o) = (p-c)/(p-v)$. The supplier's profit with a pull contract, $\pi_s(q)$, satisfies
--   $$
--   \pi_s'(q) = (p - v)\big(1 - F(q^o)\big) j(q) h(q) \quad \text{for every } q > 0,
--   $$
--   where $j(q) = S(q)/(1-F(q))$ and $h(q) = f(q)/(1-F(q))$, and $\pi_s$ is strictly increasing on $[0, \infty)$.
--
--   With pull, the supplier always wants a larger quantity; this drives the pull Pareto set $[q^*, q^o]$.
--
--   **Formalization Note** The paper writes "increasing" with the derivative $\ge 0$; the strictly increasing reading is true under the standing assumptions.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 227, Eq. (9)

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Eq. (9), p. 227: the pull supplier's profit is increasing in `q`, with
`π_s'(q) = (p - v)(1 - F(q^o)) j(q) h(q)`. -/
theorem pull_supplier_increasing (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo : cdf μ qo = (p - c) / (p - v)) :
    (∀ q : ℝ, 0 < q → HasDerivAt (pullSupplierProfit μ c v)
      ((p - v) * (1 - cdf μ qo) * j μ q * hazard μ f q) q) ∧
    StrictMonoOn (pullSupplierProfit μ c v) (Set.Ici 0) := by sorry

end CachonPushPull.Pareto
