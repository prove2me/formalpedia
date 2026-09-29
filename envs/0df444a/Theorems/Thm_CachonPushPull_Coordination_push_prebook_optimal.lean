-- Prove2me | Theorems.Thm_CachonPushPull_Coordination_push_prebook_optimal
-- name    : CachonPushPull.Coordination.push_prebook_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:34:20.649554+00:00
-- url     : https://prove2.me/theorems/84a7b647-050c-4143-b7bf-068c616b9dd2
-- title:
--   Eq. (3) — in push mode the retailer prebooks $q$ with $F(q) = (p - \hat w_1)/(p - v)$
-- statement:
--   Let demand satisfy the standing assumptions and $v < c < p$. In push mode the supplier produces exactly the prebook, and the retailer's profit from a prebook $q$ at price $\hat w_1$ is
--   $$
--   \hat\pi_r(q, \hat w_1) = (p - v)S(q) - (\hat w_1 - v)q .
--   $$
--   For every $v < \hat w_1 \le p$ there is $q \ge 0$ with
--   $$
--   F(q) = \frac{p - \hat w_1}{p - v},
--   $$
--   and every such $q$ is the unique maximizer of $\hat\pi_r(\cdot, \hat w_1)$ over $[0, \infty)$.
--
--   In the proof of Theorem 7 this shows that, with $w_2 = p$ and $w_1 \ge c$, the retailer never gains by prebooking more than $q^o$.
--
--   **Formalization Note** The paper writes "the optimal prebook is implicitly defined by"; the statement reads this as existence plus unique maximization. The paper's push contracts have $\hat w_1 < p$; the statement also covers $\hat w_1 = p$ (where the optimal prebook is $0$) and allows any $\hat w_1 > v$.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 227, Section 4.2, Eq. (3)

import Mathlib
import Definitions.Def_CachonPushPull_Coordination_Game

namespace CachonPushPull.Coordination

open MeasureTheory ProbabilityTheory

/-- Eq. (3), p. 227: in push mode (the supplier produces exactly the prebook) the retailer's
profit is `π̂_r(q, ŵ₁) = (p - v) S(q) - (ŵ₁ - v) q`. For every prebook price `v < ŵ₁ ≤ p` a
prebook `q ≥ 0` with `F(q) = (p - ŵ₁)/(p - v)` exists, and every such `q` is the unique maximizer
of `π̂_r(·, ŵ₁)` over `[0, ∞)`. -/
theorem push_prebook_optimal (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (w : ℝ) (hvw : v < w) (hwp : w ≤ p) :
    (∃ q : ℝ, 0 ≤ q ∧ cdf μ q = (p - w) / (p - v)) ∧
    ∀ q : ℝ, 0 ≤ q → cdf μ q = (p - w) / (p - v) →
      ∀ y : ℝ, 0 ≤ y → y ≠ q →
        (p - v) * S μ y - (w - v) * y < (p - v) * S μ q - (w - v) * q := by sorry

end CachonPushPull.Coordination
