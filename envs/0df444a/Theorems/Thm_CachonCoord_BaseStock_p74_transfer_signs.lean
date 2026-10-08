-- Prove2me | Theorems.Thm_CachonCoord_BaseStock_p74_transfer_signs
-- name    : CachonCoord.BaseStock.p74_transfer_signs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:55:22.401657+00:00
-- url     : https://prove2.me/theorems/583c4077-871f-4289-975b-ad53963d2fb2
-- title:
--   §6.7.1, p. 74 — signs of the transfer rates; t_B ranges over [−β_s, β_r)
-- statement:
--   In the single-location base-stock model with holding cost rate $h_r>0$ and backorder cost rates $\beta_r,\beta_s>0$, $\beta=\beta_r+\beta_s$, consider the contracts of Eq. (33): for $\lambda\in(0,1]$ the supplier pays the retailer at the rates
--   $$t_I=(1-\lambda)h_r,\qquad t_B=\beta_r-\lambda\beta$$
--   per unit of expected inventory and per unit of expected backorders. Then:
--
--   1. for every $\lambda\in(0,1]$, $t_I\ge0$, and $t_I>0$ exactly when $\lambda<1$ (the supplier subsidizes the retailer's holding cost);
--   2. as $\lambda$ ranges over $(0,1]$, $t_B$ takes exactly the values in $[-\beta_s,\beta_r)$;
--   3. some contract in the family has $t_B>0$, i.e. the supplier subsidizes the retailer's backorders.
--
--   The result describes which way money flows under the coordinating contracts: the inventory term is never a penalty, while the backorder term can be either a penalty or a subsidy.
--
--   **Formalization Note** The page says the conjecture $t_I>0$ "is valid when $\lambda\in(0,1]$"; at $\lambda=1$ the printed formula gives $t_I=0$, so the statement here is $t_I\ge0$ with strict positivity exactly for $\lambda<1$. Positive rates are payments from the supplier to the retailer, as on p. 73.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.7.1, paragraph after Eq. (33), p. 74

import Mathlib
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, p. 74, the paragraph after (33): signs of the transfer rates
`t_I = (1 - λ)h_r` and `t_B = β_r - λβ` over the family `λ ∈ (0, 1]`.
The inventory subsidy is nonnegative and strictly positive exactly when `λ < 1`
(the page's "t_I > 0 … valid when λ ∈ (0, 1]" fails at `λ = 1`, where `t_I = 0`);
the backorder rates fill exactly `[-β_s, β_r)`, and some contract has `t_B > 0`. -/
theorem p74_transfer_signs (M : Model) :
    (∀ lam : ℝ, 0 < lam → lam ≤ 1 → 0 ≤ M.tI lam ∧ (0 < M.tI lam ↔ lam < 1)) ∧
    M.tB '' Set.Ioc 0 1 = Set.Ico (-M.bs) M.br ∧
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧ 0 < M.tB lam := by sorry

end CachonCoord.BaseStock
