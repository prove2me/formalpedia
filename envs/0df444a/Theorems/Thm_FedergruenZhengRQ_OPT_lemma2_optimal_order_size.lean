-- Prove2me | Theorems.Thm_FedergruenZhengRQ_OPT_lemma2_optimal_order_size
-- name    : FedergruenZhengRQ.OPT.lemma2_optimal_order_size
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:57:13.466156+00:00
-- url     : https://prove2.me/theorems/0dfb24b8-6f73-44ed-b77a-42dbf9247c96
-- title:
--   Lemma 2 — the smallest $q$ with $C^*(q)\le G(y_{q+1})$ is an optimal order size
-- statement:
--   Let $\kappa>0$, let $-G$ be unimodal on the integers with $\lim_{|y|\to\infty}G(y)=\infty$, let $y_1$ be a global minimizer of $G$, and let $y_Q$ and $C^*(Q)=\big[\kappa+\sum_{i=1}^{Q}G(y_i)\big]/Q$ be as in §2. Then
--
--   1. some integer $q\ge1$ satisfies $C^*(q)\le G(y_{q+1})$; and
--   2. if $q\ge1$ satisfies $C^*(q)\le G(y_{q+1})$ while every $q'$ with $1\le q'<q$ satisfies $G(y_{q'+1})<C^*(q')$ (that is, $q$ is the smallest integer with the property), then $q$ is an optimal order size:
--   $$C^*(q)\;\le\;C^*(Q)\qquad\text{for every integer } Q\ge1 .$$
--
--   Combined with Lemma 1 this reduces the joint optimization over $(r,Q)$ to scanning $Q=1,2,\dots$ until the first $q$ with $C^*(q)\le G(y_{q+1})$.
--
--   **Formalization Note.** The paper's "$Q^*$" is the optimal order size, a minimizer of $C^*(\cdot)$ over $Q\ge1$, which need not be unique; the lemma is stated as existence of the smallest $q$ with the property plus its optimality. Existence (item 1) is not stated on the page; it follows from coercivity, which is the paper's standing assumption and is needed: for constant $G$ no $q$ has the property. The proof printed on p. 811 writes "$C(Q)-C(Q^*)=[\sum_{i=Q^*+1}^{Q}G(y_i)-(Q-Q^*)C^*(Q)]/Q$"; the correct identity has $C^*(Q)-C^*(Q^*)$ on the left and $C^*(Q^*)$ inside the bracket. This affects only the proof.
-- source:
--   Federgruen and Zheng, An Efficient Algorithm for Computing an Optimal (r, Q) Policy in Continuous Review Stochastic Inventory Systems, Oper. Res. 40(4) (1992), Lemma 2 (p. 811)

import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

namespace FedergruenZhengRQ.OPT

theorem lemma2_optimal_order_size (κ : ℝ) (hκ : 0 < κ) (G : ℤ → ℝ)
    (hG : NegUnimodal G) (hco : Coercive G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t) :
    (∃ q : ℕ, 1 ≤ q ∧ Cstar κ G y₁ q ≤ G (y G y₁ (q + 1))) ∧
    ∀ q : ℕ, 1 ≤ q → Cstar κ G y₁ q ≤ G (y G y₁ (q + 1)) →
      (∀ q' : ℕ, 1 ≤ q' → q' < q → G (y G y₁ (q' + 1)) < Cstar κ G y₁ q') →
      ∀ Q : ℕ, 1 ≤ Q → Cstar κ G y₁ q ≤ Cstar κ G y₁ Q := by sorry

end FedergruenZhengRQ.OPT
