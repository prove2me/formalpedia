-- Prove2me | Theorems.Thm_FedergruenZhengRQ_OPT_eq6_cost_recursion
-- name    : FedergruenZhengRQ.OPT.eq6_cost_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:57:08.97518+00:00
-- url     : https://prove2.me/theorems/3c4ff93e-9aa9-4767-ba53-321c85666303
-- title:
--   Eq. (6) — $C^*(Q+1)=[QC^*(Q)+G(y_{Q+1})]/(Q+1)$
-- statement:
--   Let $\kappa\in\mathbb R$, $G:\mathbb Z\to\mathbb R$, $y_1\in\mathbb Z$, let $y_1,y_2,\dots$ be the §2 sequence and $C^*(Q)=\big[\kappa+\sum_{i=1}^{Q}G(y_i)\big]/Q$. For every integer $Q\ge1$,
--   $$C^*(Q+1)=\frac{Q\,C^*(Q)+G(y_{Q+1})}{Q+1},$$
--   and $C^*(Q+1)<C^*(Q)$ if and only if $G(y_{Q+1})<C^*(Q)$.
--
--   The recursion lets the algorithm update the optimal cost for the next order quantity in constant time, and the comparison tells it when increasing $Q$ stops paying off.
--
--   **Formalization Note.** With $C^*$ defined by the page's formula this is an algebraic identity and holds without the standing assumptions, which are omitted (a generalization). $Q\ge1$ is required: Lean's $C^*(0)=\kappa/0=0$ breaks the identity at $Q=0$.
-- source:
--   Federgruen and Zheng, An Efficient Algorithm for Computing an Optimal (r, Q) Policy in Continuous Review Stochastic Inventory Systems, Oper. Res. 40(4) (1992), (6) and the sentence after it (p. 811)

import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

namespace FedergruenZhengRQ.OPT

theorem eq6_cost_recursion (κ : ℝ) (G : ℤ → ℝ) (y₁ : ℤ) (Q : ℕ) (hQ : 1 ≤ Q) :
    Cstar κ G y₁ (Q + 1) = ((Q : ℝ) * Cstar κ G y₁ Q + G (y G y₁ (Q + 1))) / ((Q : ℝ) + 1) ∧
    (Cstar κ G y₁ (Q + 1) < Cstar κ G y₁ Q ↔ G (y G y₁ (Q + 1)) < Cstar κ G y₁ Q) := by sorry

end FedergruenZhengRQ.OPT
