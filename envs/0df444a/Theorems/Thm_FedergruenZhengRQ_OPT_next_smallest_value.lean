-- Prove2me | Theorems.Thm_FedergruenZhengRQ_OPT_next_smallest_value
-- name    : FedergruenZhengRQ.OPT.next_smallest_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:56:37.440001+00:00
-- url     : https://prove2.me/theorems/9fcec9f5-4393-4c30-b714-5966b3bb924b
-- title:
--   Figure 1 — the $(q+1)$st smallest value of $G$ is at $L-1$ or $U+1$
-- statement:
--   Let $-G$ be unimodal on the integers, let $y_1$ be a global minimizer of $G$, and let $y_Q$, $[L(Q),R(Q)]$ be the sequence and windows of §2. For every $Q\ge1$, the next point $y_{Q+1}$ (which is $L(Q)-1$ or $R(Q)+1$) has the smallest $G$-value outside the window, and the values along the sequence do not decrease:
--   $$G(y_{Q+1})\le G(t)\quad\text{for every integer } t\notin[L(Q),R(Q)],\qquad G(y_Q)\le G(y_{Q+1}).$$
--
--   This is the content of the caption of Figure 1. The monotonicity $G(y_1)\le G(y_2)\le\cdots$ is used, without being stated, in the proof of Lemma 2.
--
--   **Formalization Note.** The caption's $L$, $U$ are the window's ends $L(Q)$, $R(Q)$ and its $q$ is $Q$.
-- source:
--   Federgruen and Zheng, An Efficient Algorithm for Computing an Optimal (r, Q) Policy in Continuous Review Stochastic Inventory Systems, Oper. Res. 40(4) (1992), caption of Figure 1 (p. 809)

import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

namespace FedergruenZhengRQ.OPT

theorem next_smallest_value (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ)
    (hy₁ : ∀ t, G y₁ ≤ G t) (Q : ℕ) (hQ : 1 ≤ Q) :
    (∀ t : ℤ, t ∉ Finset.Icc (L G y₁ Q) (R G y₁ Q) → G (y G y₁ (Q + 1)) ≤ G t) ∧
    G (y G y₁ Q) ≤ G (y G y₁ (Q + 1)) := by sorry

end FedergruenZhengRQ.OPT
