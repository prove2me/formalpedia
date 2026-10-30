-- Prove2me | Theorems.Thm_BudgetMgmt_Profit_G1_reserve_c_le_lower_end
-- name    : BudgetMgmt.Profit.G1_reserve_c_le_lower_end
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-29T21:06:27.590149+00:00
-- url     : https://prove2.me/theorems/58e4385b-c697-4909-981e-b38b0f2785bb
-- title:
--   Reserve pricing, pp. ec 9, ec 41–42 — $G^R_1(c)\le G^R_1(\hat s_1)$ at the lower end $\hat s_1=\inf\hat S_1$
-- statement:
--   Consider a symmetric correlated instance with opportunity cost $c>0$ and common budget $B_1$, whose value distribution satisfies Assumption 1 (p. ec 9), and let $\bar r$ be an admissible upper end of reserve pricing's parameter space (inside the support, and for every buyer and every profile of the others in $[c,\bar r]$ the upper end meets the budget and the lower-bound constraint $r_i\ge\underline r_i(r_{-i})$). Let
--
--   $$\hat S_1=\{r_1\in[c,\bar r]:\ r_1\vec1\in S'\}$$
--
--   be the symmetric restricted parameter space of reserve pricing (p. ec 41), that is, the $r_1\in[c,\bar r]$ with $\xi_i(r_1,r_1\vec1_{-i})\ge1$ for every buyer $i$ whenever $r_1$ is inside the support, and let $\hat s_1=\inf\hat S_1$ be its lower end. Writing $G^R_1(r_1)$ for one buyer's expected expenditure when all buyers use reserve price $r_1$, the statement is
--
--   $$G^R_1(c)\le G^R_1(\hat s_1).$$
--
--   This is the comparison of reserve pricing at its lower end with reserve pricing at $c$ — which coincides with thresholding at $c$, a second-price auction with reserve $c$ — needed in the proof of Theorem 4.2 (Reserve Pricing $\ge_{SIF}$ Thresholding, pp. ec 44–45) when reserve pricing's budget is slack at equilibrium. It reflects the derivative formula $\partial G^R_1/\partial r_1=F_{-1}(r_1\vec1_{-1})\bar F_1(r_1\mid x_{-1}\le r_1\vec1_{-1})(1-\xi_1(r_1,r_1\vec1_{-1}))$ (p. ec 42) together with $\xi_i(r_i,r_i\vee r_{-i})<1$ for $r_i<\underline r_i(r_{-i})$ (p. ec 9).
--
--   **Formalization Note** The space $\hat S_1$ is `ShatR P rbar` of the model definition; the lower-bound constraint is encoded through $\xi_i\ge1$ as in `ResConstr`.
-- source:
--   Balseiro, Kim, Mahdian & Mirrokni, Budget management strategies in repeated auctions, SSRN 2858261 (version of July 8, 2020), p. ec 42 (derivative of $G^R_1$), p. ec 9 ($\xi_i<1$ below $\underline r_i(r_{-i})$, space $S'$), p. ec 41 ($\hat S_1$); used in the proof of Theorem 4.2, pp. ec 44–45

import Mathlib
import Definitions.Def_BudgetMgmt_Profit_Model

namespace BudgetMgmt.Profit

/-- Reserve pricing in the correlated setting (pp. ec 9, ec 41–42): under Assumption 1 and for every
admissible upper end `r̄`, one buyer's symmetric expenditure at the lower end `ŝ₁ = inf Ŝ₁` of the
restricted symmetric space is at least its value at the opportunity cost, `G^R₁(c) ≤ G^R₁(ŝ₁)`
(on `[c, ŝ₁)` one has `ξ₁(r₁, r₁ 1⃗) < 1`, so `∂G^R₁/∂r₁ ≥ 0` there). -/
theorem G1_reserve_c_le_lower_end {n : ℕ} [NeZero n] (P : SymInstance n) (hA : Assumption1 P)
    (rbar : ℝ) (hR : AdmissibleR P rbar) :
    G1 P .reserve P.c ≤ G1 P .reserve (sInf (ShatR P rbar)) := by sorry

end BudgetMgmt.Profit
