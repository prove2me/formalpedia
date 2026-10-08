-- Prove2me | Theorems.Thm_FedergruenZhengRQ_OPT_algorithmOPT_optimal
-- name    : FedergruenZhengRQ.OPT.algorithmOPT_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:57:26.399659+00:00
-- url     : https://prove2.me/theorems/670465cd-4950-4ea1-a03d-65aaf18c5160
-- title:
--   Theorem 1 — Algorithm OPT determines an optimal $(r^*,Q^*)$ policy
-- statement:
--   Let $\kappa>0$ and let $G:\mathbb Z\to\mathbb R$ be such that $-G$ is unimodal and $\lim_{|y|\to\infty}G(y)=\infty$, and let $C(r,Q)=\big[\kappa+\sum_{y=r+1}^{r+Q}G(y)\big]/Q$ be the long-run average cost (1) of the $(r,Q)$ policy. Let $y_1$ be any integer minimizing $G$. Run Step 1 of Algorithm OPT from $y_1$. Then the algorithm stops after finitely many passes, and its output $(r,Q)$ satisfies $Q\ge1$ and
--   $$C(r,Q)\;\le\;C(r',Q')\qquad\text{for every integer } r' \text{ and every integer } Q'\ge1 .$$
--   Precisely: there is $N$ such that for every budget $n\ge N$ the run with $n$ passes returns an output, and that output is a jointly optimal $(r,Q)$ policy.
--
--   This is the paper's main result: an exact and very cheap procedure for the optimal reorder point and order quantity in every continuous-review model whose cost has the form (1).
--
--   **Formalization Note.** Only the first sentence of Theorem 1 is formalized; the operation count (13, resp. 11, times the work to evaluate $P_{r^*+Q^*}$) is not. Step 0 (a linear scan from $0$ for the minimizer, under the paper's assumption $y_1>0$) is replaced by "$y_1$ is a given global minimizer of $G$", the paper's own setup in §2 and its p. 812 remark that Step 0 may be replaced by a bisection search; Step 0 under unimodality alone can stop at a non-minimizer on a plateau. "The optimal $(r^*,Q^*)$" is read as "an optimal": minimizers need not be unique. Optimality is over all integer $r'$ and all $Q'\ge1$ ($C(r,0)$ is undefined on the page and $0$ in Lean). Coercivity is necessary: for constant $G$ the loop never stops.
-- source:
--   Federgruen and Zheng, An Efficient Algorithm for Computing an Optimal (r, Q) Policy in Continuous Review Stochastic Inventory Systems, Oper. Res. 40(4) (1992), Theorem 1 (p. 812); Algorithm OPT (p. 811)

import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

namespace FedergruenZhengRQ.OPT

theorem algorithmOPT_optimal (κ : ℝ) (hκ : 0 < κ) (G : ℤ → ℝ) (hG : NegUnimodal G)
    (hco : Coercive G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ r : ℤ, ∃ Q : ℕ, optRun κ G y₁ n = some (r, Q) ∧ 1 ≤ Q ∧
      ∀ r' : ℤ, ∀ Q' : ℕ, 1 ≤ Q' → cost κ G r Q ≤ cost κ G r' Q' := by sorry

end FedergruenZhengRQ.OPT
