-- Prove2me | Theorems.Thm_DemandSubstitution_Comparison_eq1_profit_underage_overage
-- name    : DemandSubstitution.Comparison.eq1_profit_underage_overage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:16.34535+00:00
-- url     : https://prove2.me/theorems/0622b2ba-9c0e-4d57-bc73-2509579fa28b
-- title:
--   Equation (1), p. 3 — π = E Σ_i [u_i D^s_i − u_i (D^s_i − Q_i)⁺ − o_i (Q_i − D^s_i)⁺]
-- statement:
--   In the $n$-product substitution model, let $u_i = r_i - c_i$, $o_i = c_i - s_i$ and $D^s_i = D_i + \sum_{j\ne i} a_{ji}(D_j - Q_j)^+$. For every stocking vector $Q$, the centralized expected profit
--   $\pi(Q) = \mathbb E \sum_i [ r_i \min(D^s_i, Q_i) - c_i Q_i + s_i (Q_i - D^s_i)^+ ]$
--   can be rewritten in underage/overage form:
--   $$\pi(Q) = \mathbb E \sum_i \Big[u_i D^s_i - u_i (D^s_i - Q_i)^+ - o_i (Q_i - D^s_i)^+\Big]. \tag{1}$$
--
--   The form (1) separates the profit under perfect information, $\mathbb E\sum_i u_i D^s_i$, which here depends on the stocking decisions, from the expected underage and overage costs; it is the form that is differentiated to obtain the optimality conditions.
--
--   **Formalization Note** The identity is stated for every real vector $Q$ and every measure on $\mathbb R^n$; the two integrands agree pointwise.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 3, §2.1, equation (1)

import Mathlib
import Definitions.Def_DemandSubstitution_Comparison_Setting

open MeasureTheory

namespace DemandSubstitution.Comparison

/-- Equation (1), p. 3: the centralized expected profit in underage/overage form,
`π = E ∑_i [u_i D^s_i − u_i (D^s_i − Q_i)⁺ − o_i (Q_i − D^s_i)⁺]`, for every stocking vector `Q`. -/
theorem eq1_profit_underage_overage {n : ℕ} (M : Model n) (μ : Measure (Fin n → ℝ))
    (Q : Fin n → ℝ) :
    centralProfit M μ Q =
      ∫ x, ∑ i, (M.u i * Ds M Q x i - M.u i * max (Ds M Q x i - Q i) 0
        - M.o i * max (Q i - Ds M Q x i) 0) ∂μ := by sorry

end DemandSubstitution.Comparison
