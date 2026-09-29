-- Prove2me | Theorems.Thm_CachonPushPull_ShippingCost_supplier_best_response
-- name    : CachonPushPull.ShippingCost.supplier_best_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:37:33.529887+00:00
-- url     : https://prove2.me/theorems/18e3b68d-ecd3-4591-a81a-75ce110e45fc
-- title:
--   Eqs. (20)–(21) with $w_2 - \tau$ — the supplier's best response is $\max\{y, q_s\}$
-- statement:
--   Let the supplier pay a shipping and handling cost $\tau > 0$ per at-once unit, let $w_2 \le p$ and $c \le w_2 - \tau$. Then:
--
--   1. there is $q_s \ge 0$ with
--   $$
--   F(q_s) = \frac{w_2 - \tau - c}{w_2 - \tau - v};
--   $$
--   2. for every prebook price $w_1$ and every prebook $y \ge 0$, the supplier's profit $q \mapsto \pi_s(y, q)$ is concave on $q \ge y$, and her best responses to $y$ are exactly $q = \max\{y, q_s\}$ (for any $q_s$ as in 1);
--   3. the shipping cost reduces the optimal production: if $q_s^0 \ge 0$ satisfies Eq. (21) without shipping cost, $F(q_s^0) = (w_2 - c)/(w_2 - v)$, then $q_s < q_s^0$.
--
--   In particular the supplier's production is independent of $w_1$, and independent of $y$ whenever $y < q_s$. This is the input of the proof of Theorem 8 on the supplier's side.
--
--   **Formalization Note** The hypothesis $c \le w_2 - \tau$ is the domain of the paper's formula ($q_s \ge 0$). When $w_2 - \tau < c$ the supplier never produces beyond the prebook; that case is not part of this statement. The paper's "reduces" is read as a strict decrease, which is what the formula gives for $\tau > 0$.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 234, proof of Theorem 8 (Eqs. (20)-(21) of p. 233 with w2 replaced by w2 - tau)

import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Game

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

/-- Eqs. (20)–(21) with `w₂` replaced by `w₂ - τ` (proof of Theorem 8, p. 234). Let `τ > 0` be the
supplier's shipping and handling cost per at-once unit, `w₂ ≤ p`, and `c ≤ w₂ - τ`. Then:
1. a quantity `q_s ≥ 0` with `F(q_s) = (w₂ - τ - c)/(w₂ - τ - v)` exists;
2. for every prebook price `w₁` and prebook `y ≥ 0`, the supplier's profit is concave in the
   production `q ≥ y`, and her best responses to `y` are exactly `q = max {y, q_s}` (so they do
   not depend on `w₁`, and not on `y` when `y < q_s`);
3. the shipping cost reduces the optimal production: `q_s` is strictly smaller than the
   `q_s⁰ ≥ 0` of Eq. (21) without shipping cost, `F(q_s⁰) = (w₂ - c)/(w₂ - v)`. -/
theorem supplier_best_response (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (τ : ℝ) (hτ : 0 < τ) (w₂ : ℝ) (hcw₂ : c ≤ w₂ - τ) (hw₂p : w₂ ≤ p) :
    (∃ qs : ℝ, 0 ≤ qs ∧ cdf μ qs = (w₂ - τ - c) / (w₂ - τ - v)) ∧
    (∀ w₁ y : ℝ, 0 ≤ y →
      ConcaveOn ℝ (Set.Ici y) (supplierProfit μ c v τ w₁ w₂ y) ∧
      ∀ qs : ℝ, 0 ≤ qs → cdf μ qs = (w₂ - τ - c) / (w₂ - τ - v) →
        ∀ q : ℝ, IsSupplierBestResponse μ c v τ w₁ w₂ y q ↔ q = max y qs) ∧
    ∀ qs qs₀ : ℝ, 0 ≤ qs → cdf μ qs = (w₂ - τ - c) / (w₂ - τ - v) →
      0 ≤ qs₀ → cdf μ qs₀ = (w₂ - c) / (w₂ - v) → qs < qs₀ := by sorry

end CachonPushPull.ShippingCost
