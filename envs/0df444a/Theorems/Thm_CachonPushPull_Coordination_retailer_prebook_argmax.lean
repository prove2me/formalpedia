-- Prove2me | Theorems.Thm_CachonPushPull_Coordination_retailer_prebook_argmax
-- name    : CachonPushPull.Coordination.retailer_prebook_argmax
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:33:38.478998+00:00
-- url     : https://prove2.me/theorems/d7d78e25-53a8-4867-8b6e-c9bdbef1c7fd
-- title:
--   Eq. (22) — the retailer's prebook $y_r$ with $F(y_r) = (w_2-w_1)/(w_2-v)$ is the unique maximizer of $\pi_r(\cdot, q)$
-- statement:
--   Let demand satisfy the standing assumptions and $v < c < p$. Fix a contract with $c \le w_1 \le w_2 \le p$ and a production quantity $q$. Consider the retailer's profit
--   $$
--   \pi_r(y, q) = -(w_1 - v)y + (p - v)S(y) + (p - w_2)(S(q) - S(y)), \qquad y \ge 0 .
--   $$
--   Then:
--
--   1. $y \mapsto \pi_r(y, q)$ is concave on $[0, \infty)$;
--   2. there is $y_r \ge 0$ with
--   $$
--   F(y_r) = \frac{w_2 - w_1}{w_2 - v};
--   $$
--   3. every such $y_r$ is the unique maximizer of $y \mapsto \pi_r(y, q)$ over $[0, \infty)$: $\pi_r(y, q) < \pi_r(y_r, q)$ for every $y \ge 0$ with $y \ne y_r$.
--
--   Hence, as long as the retailer anticipates that production exceeds his prebook, his optimal prebook does not depend on the supplier's production.
--
--   **Formalization Note** The paper writes $y_r = \arg\max \pi_r(y, q)$; the statement takes the unique-maximizer reading, over all $y \ge 0$, for the displayed formula. The formula is the retailer's profit only when $y \le q$; the statement is about the formula itself.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 233, Section 4.5, Eq. (22)

import Mathlib
import Definitions.Def_CachonPushPull_Coordination_Game

namespace CachonPushPull.Coordination

open MeasureTheory ProbabilityTheory

/-- Eq. (22), p. 233: under a contract with `c ≤ w₁ ≤ w₂ ≤ p` and any fixed production `q`, the
retailer's profit `π_r(y, q)` is concave in the prebook `y ≥ 0`, a prebook `y_r ≥ 0` with
`F(y_r) = (w₂ - w₁)/(w₂ - v)` exists, and every such `y_r` is the unique maximizer of
`y ↦ π_r(y, q)` over `y ≥ 0`. -/
theorem retailer_prebook_argmax (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (w₁ w₂ : ℝ) (hcw₁ : c ≤ w₁) (hw₁₂ : w₁ ≤ w₂) (hw₂p : w₂ ≤ p) (q : ℝ) :
    ConcaveOn ℝ (Set.Ici 0) (fun y : ℝ => retailerProfit μ p v w₁ w₂ y q) ∧
    (∃ yr : ℝ, 0 ≤ yr ∧ cdf μ yr = (w₂ - w₁) / (w₂ - v)) ∧
    ∀ yr : ℝ, 0 ≤ yr → cdf μ yr = (w₂ - w₁) / (w₂ - v) →
      ∀ y : ℝ, 0 ≤ y → y ≠ yr →
        retailerProfit μ p v w₁ w₂ y q < retailerProfit μ p v w₁ w₂ yr q := by sorry

end CachonPushPull.Coordination
