-- Prove2me | Theorems.Thm_CachonPushPull_Pareto_push_supplier_unimodal
-- name    : CachonPushPull.Pareto.push_supplier_unimodal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:26:20.399984+00:00
-- url     : https://prove2.me/theorems/47d2c273-ccfa-4cb1-abd7-3a9f13a1a104
-- title:
--   Lariviere–Porteus: under IGFR the push supplier's profit $\hat\pi_s(q)$ is unimodal
-- statement:
--   Let demand satisfy the standing assumptions (in particular IGFR) and $v < c < p$. The supplier's profit with a push contract,
--   $$
--   \hat\pi_s(q) = \big(\hat w_1(q) - c\big) q ,
--   $$
--   is unimodal on $[0, \infty)$: there is $\hat q > 0$ such that $\hat\pi_s$ is strictly increasing on $[0, \hat q]$ and strictly decreasing on $[\hat q, \infty)$.
--
--   The paper cites this from Lariviere and Porteus (2001). It makes the supplier's preferred push contract $\hat q^* = \arg\max \hat\pi_s$ unique and yields the push Pareto set.
--
--   **Formalization Note** "Unimodal" is read as strictly up then strictly down with an interior peak. A related platform statement (Snyder–Shen Theorem 14.3) assumes additionally a nonnegative salvage value, finite mean and a continuous positive density, and only a weakly increasing generalized failure rate, so it is not reused.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 227, Section 4.2 (citing Lariviere and Porteus 2001)

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- §4.2, p. 227 (Lariviere and Porteus 2001): under IGFR the push supplier's profit
`π̂_s(q)` is unimodal in `q`. -/
theorem push_supplier_unimodal (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    ∃ qh : ℝ, 0 < qh ∧
      StrictMonoOn (pushSupplierProfit μ p c v) (Set.Icc 0 qh) ∧
      StrictAntiOn (pushSupplierProfit μ p c v) (Set.Ici qh) := by sorry

end CachonPushPull.Pareto
