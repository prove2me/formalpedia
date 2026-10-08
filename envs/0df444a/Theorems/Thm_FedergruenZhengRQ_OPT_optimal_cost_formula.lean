-- Prove2me | Theorems.Thm_FedergruenZhengRQ_OPT_optimal_cost_formula
-- name    : FedergruenZhengRQ.OPT.optimal_cost_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:57:00.420792+00:00
-- url     : https://prove2.me/theorems/503d2769-ef4c-4f49-8494-9f140efb1754
-- title:
--   §2 — $C^*(Q)=\min_r C(r,Q)=[\kappa+\sum_{i=1}^Q G(y_i)]/Q$
-- statement:
--   Let $\kappa>0$, let $-G$ be unimodal on the integers, let $y_1$ be a global minimizer of $G$, and let $y_1,y_2,\dots$ be the §2 sequence. For every integer $Q\ge1$, the minimum of the cost (1) over all integer reorder points exists and equals the page's formula:
--   $$\min_{r\in\mathbb Z}C(r,Q)\;=\;\Big[\kappa+\sum_{i=1}^{Q}G(y_i)\Big]\Big/Q\;=:\;C^*(Q).$$
--
--   It gives the optimal cost for each order quantity in closed form along the sequence $y_Q$, which is what makes the recursion (6) and Lemma 2 possible.
--
--   **Formalization Note.** Stated as: $C^*(Q)$ is the least element of $\{C(r,Q):r\in\mathbb Z\}$, so both attainment and minimality are asserted.
-- source:
--   Federgruen and Zheng, An Efficient Algorithm for Computing an Optimal (r, Q) Policy in Continuous Review Stochastic Inventory Systems, Oper. Res. 40(4) (1992), §2, display before (6) (p. 811)

import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

namespace FedergruenZhengRQ.OPT

theorem optimal_cost_formula (κ : ℝ) (hκ : 0 < κ) (G : ℤ → ℝ) (hG : NegUnimodal G)
    (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t) (Q : ℕ) (hQ : 1 ≤ Q) :
    IsLeast (Set.range fun r : ℤ => cost κ G r Q) (Cstar κ G y₁ Q) := by sorry

end FedergruenZhengRQ.OPT
