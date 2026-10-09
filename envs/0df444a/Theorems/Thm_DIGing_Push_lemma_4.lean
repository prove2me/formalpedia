-- Prove2me | Theorems.Thm_DIGing_Push_lemma_4
-- name    : DIGing.Push.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:56:03.917977+00:00
-- url     : https://prove2.me/theorems/c2f95d0e-927d-4ade-9e55-ab675cd66876
-- title:
--   Lemma 4, p. 9 — bounded norm ⇒ R-linear rate: λ^{-k}‖s(k)‖_F ≤ U for all k implies ‖s(k)‖_F ≤ Uλᵏ
-- statement:
--   Let $\lambda\in(0,1)$ and let $\mathbf s$ be a sequence of $n\times p$ matrices with $\|\mathbf s\|^\lambda_F\le U$, i.e. $\frac1{\lambda^k}\|\mathbf s(k)\|_F\le U$ for all $k$. Then
--   $$\|\mathbf s(k)\|_F\le U\lambda^k\qquad\text{for all }k\ge0,$$
--   so $\|\mathbf s(k)\|_F$ converges to $0$ at the R-linear rate $O(\lambda^k)$.
--
--   This is the last step of the proof of Theorem 18.
--
--   **Formalization Note** The page's "if $\|\mathbf s\|^\lambda_F$ is bounded" is written with an explicit bound $U$; the statement is close to unfolding the definition and is included because the paper states it and the goal's proof cites it. This statement is identical to the one in the companion DIGing mission.
-- source:
--   arXiv:1607.03218v3, Lemma 4, p. 9

import Mathlib
import Definitions.Def_DIGing_Undir_Common

namespace DIGing.Push

theorem lemma_4 {n p : ℕ} (s : ℕ → DIGing.Undir.Stack n p) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (U : ℝ) (hU : ∀ k : ℕ, DIGing.Undir.frob (s k) / lam ^ k ≤ U) :
    ∀ k : ℕ, DIGing.Undir.frob (s k) ≤ U * lam ^ k := by sorry

end DIGing.Push
