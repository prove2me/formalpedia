-- Prove2me | Theorems.Thm_CachonPushPull_Coordination_supplier_best_response
-- name    : CachonPushPull.Coordination.supplier_best_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:33:08.201985+00:00
-- url     : https://prove2.me/theorems/b404eecc-e201-438f-be4b-d03f560d8a1c
-- title:
--   Eqs. (20)–(21) — the supplier produces $\max\{y, q_s\}$ with $F(q_s) = (w_2-c)/(w_2-v)$
-- statement:
--   Let demand satisfy the standing assumptions and $v < c < p$. Fix a contract with prebook price $w_1$ (arbitrary) and at-once price $c \le w_2 \le p$, so that at-once orders are submitted. Then there is $q_s \ge 0$ with
--   $$
--   F(q_s) = \frac{w_2 - c}{w_2 - v},
--   $$
--   and for every prebook $y \ge 0$:
--
--   1. the supplier's profit $\pi_s(y, q) = (w_1 - v)y + (w_2 - v)(S(q) - S(y)) - (c - v)q$ is concave in $q$ on $[y, \infty)$;
--   2. for every $q_s \ge 0$ solving the equation above, a production $q$ is a supplier best response to $y$ if and only if $q = \max\{y, q_s\}$.
--
--   The supplier's production is therefore independent of $w_1$, and of $y$ whenever $y < q_s$; otherwise she produces exactly the prebook.
--
--   **Formalization Note** The best response is defined as a maximizer over $q \ge y$; the "if and only if" makes it unique. $q_s \ge 0$ is required because at $w_2 = c$ the equation $F(q_s) = 0$ is also solved by every negative number.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 233, Section 4.5, Eqs. (20)-(21)

import Mathlib
import Definitions.Def_CachonPushPull_Coordination_Game

namespace CachonPushPull.Coordination

open MeasureTheory ProbabilityTheory

/-- Eqs. (20)–(21), p. 233: under a contract with at-once price `c ≤ w₂ ≤ p` (so at-once orders
are submitted) and any prebook price `w₁`, a quantity `q_s ≥ 0` with
`F(q_s) = (w₂ - c)/(w₂ - v)` exists; for every prebook `y ≥ 0` the supplier's profit (20) is
concave in the production `q ≥ y`, and her best responses to `y` are exactly `q = max {y, q_s}`. -/
theorem supplier_best_response (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (w₁ w₂ : ℝ) (hcw₂ : c ≤ w₂) (hw₂p : w₂ ≤ p) :
    (∃ qs : ℝ, 0 ≤ qs ∧ cdf μ qs = (w₂ - c) / (w₂ - v)) ∧
    ∀ y : ℝ, 0 ≤ y →
      ConcaveOn ℝ (Set.Ici y) (supplierProfit μ p c v w₁ w₂ y) ∧
      ∀ qs : ℝ, 0 ≤ qs → cdf μ qs = (w₂ - c) / (w₂ - v) →
        ∀ q : ℝ, IsSupplierBestResponse μ p c v w₁ w₂ y q ↔ q = max y qs := by sorry

end CachonPushPull.Coordination
