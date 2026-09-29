-- Prove2me | Theorems.Thm_CachonPushPull_Pareto_pull_beats_push_maxima
-- name    : CachonPushPull.Pareto.pull_beats_push_maxima
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:28:25.971907+00:00
-- url     : https://prove2.me/theorems/404e83c7-d8bc-4548-9bca-82f05ff7989a
-- title:
--   Theorem 3: $\pi_r(q^*) > \hat\pi_s(\hat q^*)$, $q^* > \hat q^*$ and $\Pi(q^*) > \Pi(\hat q^*)$
-- statement:
--   Let demand satisfy the standing assumptions and $v < c < p$. The retailer's pull profit $\pi_r$ has a maximizer $q^*$ over $[0,\infty)$, the supplier's push profit $\hat\pi_s$ has a maximizer $\hat q^*$ over $[0,\infty)$, and for every such pair of maximizers
--   $$
--   \pi_r(q^*) > \hat\pi_s(\hat q^*), \qquad q^* > \hat q^*, \qquad \Pi(q^*) > \Pi(\hat q^*).
--   $$
--
--   In words: the retailer's maximum profit with pull exceeds the supplier's maximum profit with push, more inventory is carried, and the chain is more efficient. Since $\Pi^o > 0$, the last inequality is equivalent to the paper's efficiency claim $\Pi(q^*)/\Pi^o > \Pi(\hat q^*)/\Pi^o$.
--
--   **Formalization Note** Existence of both maximizers is part of the statement, so the comparison is not vacuous; the conclusion holds for every maximizer (they are unique by Theorem 2 and the unimodality of $\hat\pi_s$).
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 229, Theorem 3

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Theorem 3, p. 229: the retailer's maximum profit with pull exceeds the supplier's maximum
profit with push, `q* > q̂*`, and `Π(q*) > Π(q̂*)`. -/
theorem pull_beats_push_maxima (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    (∃ qstar : ℝ, 0 ≤ qstar ∧ IsMaxOn (pullRetailerProfit μ p c v) (Set.Ici 0) qstar) ∧
    (∃ qhat : ℝ, 0 ≤ qhat ∧ IsMaxOn (pushSupplierProfit μ p c v) (Set.Ici 0) qhat) ∧
    ∀ qstar qhat : ℝ, 0 ≤ qstar → IsMaxOn (pullRetailerProfit μ p c v) (Set.Ici 0) qstar →
      0 ≤ qhat → IsMaxOn (pushSupplierProfit μ p c v) (Set.Ici 0) qhat →
      pushSupplierProfit μ p c v qhat < pullRetailerProfit μ p c v qstar ∧
      qhat < qstar ∧
      chainProfit μ p c v qhat < chainProfit μ p c v qstar := by sorry

end CachonPushPull.Pareto
