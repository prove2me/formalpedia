-- Prove2me | Theorems.Thm_CachonPushPull_Pareto_supplier_best_reply
-- name    : CachonPushPull.Pareto.supplier_best_reply
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:29:33.356737+00:00
-- url     : https://prove2.me/theorems/79a3853a-7c2d-4594-9ed2-c8de03f68918
-- title:
--   Eqs. (20)–(21): the supplier's optimal production given a prebook $y$ is $\max\{y, q_s\}$
-- statement:
--   Let demand satisfy the standing assumptions, $v < c < p$, and let $(w_1, w_2)$ be wholesale prices with $w_2 > c$. When the retailer prebooks $y$, the supplier's profit from producing $Q \ge y$ is
--   $$
--   \pi_s(y, Q) = (w_1 - v) y + (w_2 - v)\big(S(Q) - S(y)\big) - (c - v) Q .
--   $$
--   Then
--
--   1. there is $q_s > 0$ with $F(q_s) = \dfrac{w_2 - c}{w_2 - v}$;
--   2. for every $y \ge 0$, $Q \mapsto \pi_s(y, Q)$ is concave on $[y, \infty)$;
--   3. for every $q_s$ with $F(q_s) = (w_2 - c)/(w_2 - v)$, every $y \ge 0$ and every $Q$: $Q$ is an optimal production quantity given $y$ (i.e. $Q \ge y$ and $Q$ maximizes $\pi_s(y, \cdot)$ over $[y, \infty)$) if and only if $Q = \max\{y, q_s\}$.
--
--   This describes the supplier's reply in the prebook game, which Lemma 5 uses to evaluate the retailer's option to prebook.
--
--   **Formalization Note** The hypothesis $w_2 > c$ is added: it is what makes (21) solvable ($q_s > 0$); the paper uses (21) only for such prices. The price $w_1$ affects the supplier's profit only through a constant, so it plays no role in the reply.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 233, Eq. (20) and Eq. (21)

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Eqs. (20)–(21), p. 233: with wholesale prices `(w₁, w₂)` and prebook `y`, the supplier's
profit is concave in her production and her optimal production is `max {y, q_s}`, where
`F(q_s) = (w₂ - c)/(w₂ - v)`. -/
theorem supplier_best_reply (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (w₁ w₂ : ℝ) (hw₂ : c < w₂) :
    (∃ qs : ℝ, 0 < qs ∧ cdf μ qs = (w₂ - c) / (w₂ - v)) ∧
    (∀ y : ℝ, 0 ≤ y → ConcaveOn ℝ (Set.Ici y) (apdSupplierProfit μ c v w₁ w₂ y)) ∧
    ∀ qs : ℝ, cdf μ qs = (w₂ - c) / (w₂ - v) →
      ∀ y : ℝ, 0 ≤ y → ∀ Q : ℝ,
        (IsSupplierBestReply μ c v w₁ w₂ y Q ↔ Q = max y qs) := by sorry

end CachonPushPull.Pareto
