-- Prove2me | Theorems.Thm_FedergruenZhengRQ_OPT_step1_follows_sequence
-- name    : FedergruenZhengRQ.OPT.step1_follows_sequence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:57:17.774149+00:00
-- url     : https://prove2.me/theorems/6654463d-4e09-481e-be0c-fc49d73bf9ba
-- title:
--   §2 — Step 1 of Algorithm OPT tracks $y_Q$, $C^*(Q)$ and $r^*(Q)$ of Lemmas 1 and 2
-- statement:
--   Let $\kappa\in\mathbb R$, $G:\mathbb Z\to\mathbb R$ and $y_1\in\mathbb Z$. For $Q\ge1$ write $\sigma_Q$ for the state $\big(S,Q,C^*,r,R\big)=\big(\kappa+\sum_{i=1}^{Q}G(y_i),\;Q,\;C^*(Q),\;L(Q)-1,\;R(Q)+1\big)$ built from the §2 sequence. Then Step 1 of Algorithm OPT starts in $\sigma_1$, and from $\sigma_Q$ one pass of its loop
--
--   1. stops with output $(L(Q)-1,\,Q)$ if $C^*(Q)\le G(y_{Q+1})$;
--   2. otherwise moves to $\sigma_{Q+1}$.
--
--   In words: the test "$G(r)\le G(R)$" of Step 1 is exactly the rule that chooses $y_{Q+1}$ (with ties to the left), its stopping test is Lemma 2's criterion, and its output reorder point is Lemma 1's $r^*(Q)$. This is the sense in which "Lemmas 1 and 2 clearly suggest" Algorithm OPT.
--
--   **Formalization Note.** The starting state is the one Step 0 produces when it has located $y_1$ (Step 0 itself is not formalized; see the mission description). No standing assumption is needed. Equalities of states are equalities of all five components.
-- source:
--   Federgruen and Zheng, An Efficient Algorithm for Computing an Optimal (r, Q) Policy in Continuous Review Stochastic Inventory Systems, Oper. Res. 40(4) (1992), §2, sentence before Algorithm OPT, and Algorithm OPT, Step 1 (p. 811)

import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

namespace FedergruenZhengRQ.OPT

theorem step1_follows_sequence (κ : ℝ) (G : ℤ → ℝ) (y₁ : ℤ) :
    optInit κ G y₁ = stateAt κ G y₁ 1 ∧
    ∀ Q : ℕ, 1 ≤ Q →
      optStep G (stateAt κ G y₁ Q) =
        if Cstar κ G y₁ Q ≤ G (y G y₁ (Q + 1)) then Sum.inl (L G y₁ Q - 1, Q)
        else Sum.inr (stateAt κ G y₁ (Q + 1)) := by sorry

end FedergruenZhengRQ.OPT
