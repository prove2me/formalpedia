-- Prove2me | Theorems.Thm_FedergruenZhengRQ_OPT_lemma1_reorder_point
-- name    : FedergruenZhengRQ.OPT.lemma1_reorder_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:56:51.08358+00:00
-- url     : https://prove2.me/theorems/6ec2946d-5a7c-4a24-b636-fd6eb5723466
-- title:
--   Lemma 1 — $r^*(Q)=L(Q)-1$ is an optimal reorder point for $Q$
-- statement:
--   Let $\kappa>0$, let $-G$ be unimodal on the integers, let $y_1$ be a global minimizer of $G$, and let $L(Q)$ be the left end of the §2 window after $Q$ points. For every integer $Q\ge1$, the reorder point $L(Q)-1$ minimizes the cost (1) for that $Q$:
--   $$C\big(L(Q)-1,\,Q\big)\;\le\;C(r,Q)\qquad\text{for every integer } r,$$
--   where $C(r,Q)=\big[\kappa+\sum_{y=r+1}^{r+Q}G(y)\big]/Q$.
--
--   This identifies the optimal reorder level $r^*(Q)$ for each order quantity without any search over $r$.
--
--   **Formalization Note.** Optimal reorder points need not be unique, so "$r^*(Q)=L(Q)-1$" is formalized as "$L(Q)-1$ is an optimal reorder point". The hypothesis $\kappa>0$ is the paper's standing assumption; it plays no role here.
-- source:
--   Federgruen and Zheng, An Efficient Algorithm for Computing an Optimal (r, Q) Policy in Continuous Review Stochastic Inventory Systems, Oper. Res. 40(4) (1992), Lemma 1 (p. 811)

import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

namespace FedergruenZhengRQ.OPT

theorem lemma1_reorder_point (κ : ℝ) (hκ : 0 < κ) (G : ℤ → ℝ) (hG : NegUnimodal G)
    (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t) (Q : ℕ) (hQ : 1 ≤ Q) (r : ℤ) :
    cost κ G (L G y₁ Q - 1) Q ≤ cost κ G r Q := by sorry

end FedergruenZhengRQ.OPT
