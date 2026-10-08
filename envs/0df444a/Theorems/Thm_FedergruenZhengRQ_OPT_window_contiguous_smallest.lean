-- Prove2me | Theorems.Thm_FedergruenZhengRQ_OPT_window_contiguous_smallest
-- name    : FedergruenZhengRQ.OPT.window_contiguous_smallest
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:56:28.369926+00:00
-- url     : https://prove2.me/theorems/55d32b67-27fc-4ce2-afd8-e094bceb7b22
-- title:
--   §2 — $\{y_1,\dots,y_Q\}$ is contiguous and holds the $Q$ smallest values of $G$
-- statement:
--   Let $G:\mathbb Z\to\mathbb R$ be such that $-G$ is unimodal, let $y_1$ be a global minimizer of $G$ over the integers, and let $y_1,y_2,\dots$ and the windows $[L(Q),R(Q)]$ be generated as in §2 (extend left when $G(L(Q)-1)\le G(R(Q)+1)$, otherwise right). Then for every $Q\ge1$:
--
--   1. $\{y_1,\dots,y_Q\}=\{L(Q),L(Q)+1,\dots,R(Q)\}$ and $R(Q)-L(Q)+1=Q$; so the $y_i$ are distinct and contiguous, and $L(Q)$, $R(Q)$ are their minimum and maximum;
--   2. every chosen value is at most every unchosen one: $G(y_i)\le G(t)$ for all $1\le i\le Q$ and every integer $t\notin[L(Q),R(Q)]$;
--   3. the chosen values have the least sum among all $Q$-element sets of integers:
--   $$\sum_{i=1}^{Q}G(y_i)\;\le\;\sum_{t\in T}G(t)\qquad\text{for every } T\subset\mathbb Z \text{ with } |T|=Q.$$
--
--   This is the observation that drives Lemma 1: the optimal reorder point for a given $Q$ places the window of the sum in (1) on these $Q$ points.
--
--   **Formalization Note.** Under ties, "their $G(\cdot)$ values constitute the $Q$ smallest ones" is formalized by items 2 and 3 (every chosen value is $\le$ every unchosen value, and the least-sum property used by Lemma 1). Item 1 holds for every $G$; the hypotheses are only needed for items 2 and 3. The paper defines $L(Q),R(Q)$ as $\min$ and $\max$ of $\{y_1,\dots,y_Q\}$; the formalization defines them by the window recursion and item 1 shows they agree.
-- source:
--   Federgruen and Zheng, An Efficient Algorithm for Computing an Optimal (r, Q) Policy in Continuous Review Stochastic Inventory Systems, Oper. Res. 40(4) (1992), §2, sentence after the definition of y_{Q+1} (p. 811)

import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

namespace FedergruenZhengRQ.OPT

theorem window_contiguous_smallest (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ)
    (hy₁ : ∀ t, G y₁ ≤ G t) (Q : ℕ) (hQ : 1 ≤ Q) :
    (Finset.Icc 1 Q).image (y G y₁) = Finset.Icc (L G y₁ Q) (R G y₁ Q) ∧
    R G y₁ Q - L G y₁ Q + 1 = (Q : ℤ) ∧
    (∀ i ∈ Finset.Icc 1 Q, ∀ t : ℤ, t ∉ Finset.Icc (L G y₁ Q) (R G y₁ Q) → G (y G y₁ i) ≤ G t) ∧
    (∀ T : Finset ℤ, T.card = Q → ∑ i ∈ Finset.Icc 1 Q, G (y G y₁ i) ≤ ∑ t ∈ T, G t) := by sorry

end FedergruenZhengRQ.OPT
