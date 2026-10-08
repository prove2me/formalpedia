-- Prove2me | Theorems.Thm_FedergruenZhengRQ_OPT_corollary1_reorder_monotone
-- name    : FedergruenZhengRQ.OPT.corollary1_reorder_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:56:52.674565+00:00
-- url     : https://prove2.me/theorems/3f3293d6-d7fd-4ff8-9a04-5ad888c7a652
-- title:
--   Corollary 1 — $r^*(Q)-1\le r^*(Q+1)\le r^*(Q)$
-- statement:
--   Let $\kappa>0$, let $-G$ be unimodal on the integers, let $y_1$ be a global minimizer of $G$, and let $L(Q)$ be the left end of the §2 window after $Q$ points. For every integer $Q\ge1$, the window's left end either stays or moves one step left, $L(Q+1)\in\{L(Q),\,L(Q)-1\}$, and consequently, with $r^*(Q):=L(Q)-1$,
--   $$r^*(Q)-1\;\le\;r^*(Q+1)\;\le\;r^*(Q).$$
--
--   Both $r^*(Q)$ and $r^*(Q+1)$ minimize the cost for their respective order quantities, and this chosen optimal reorder point decreases by at most one unit as the order quantity grows by one.
--
--   **Formalization Note.** $r^*(Q)$ is taken to be Lemma 1's choice $L(Q)-1$. The structural inequality holds for every $G$, while the standing assumptions ensure that this choice is optimal for both order quantities.
-- source:
--   Federgruen and Zheng, An Efficient Algorithm for Computing an Optimal (r, Q) Policy in Continuous Review Stochastic Inventory Systems, Oper. Res. 40(4) (1992), Corollary 1 and the sentence before it (p. 811)

import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

namespace FedergruenZhengRQ.OPT

theorem corollary1_reorder_monotone (κ : ℝ) (hκ : 0 < κ) (G : ℤ → ℝ)
    (hG : NegUnimodal G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t)
    (Q : ℕ) (hQ : 1 ≤ Q) :
    (L G y₁ (Q + 1) = L G y₁ Q ∨ L G y₁ (Q + 1) = L G y₁ Q - 1) ∧
    (L G y₁ Q - 1) - 1 ≤ L G y₁ (Q + 1) - 1 ∧ L G y₁ (Q + 1) - 1 ≤ L G y₁ Q - 1 ∧
    (∀ r : ℤ, cost κ G (L G y₁ Q - 1) Q ≤ cost κ G r Q) ∧
    (∀ r : ℤ, cost κ G (L G y₁ (Q + 1) - 1) (Q + 1) ≤ cost κ G r (Q + 1)) := by sorry

end FedergruenZhengRQ.OPT
