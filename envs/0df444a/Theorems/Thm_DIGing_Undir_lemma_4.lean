-- Prove2me | Theorems.Thm_DIGing_Undir_lemma_4
-- name    : DIGing.Undir.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:15.663214+00:00
-- url     : https://prove2.me/theorems/f07e70c2-29fe-462e-b13b-aa79d4202f31
-- title:
--   Lemma 4, p. 9 — bounded ‖s‖^λ_F implies the R-linear rate ‖s(k)‖_F ≤ Uλᵏ
-- statement:
--   Let $\lambda\in(0,1)$ and let $\mathbf s(0),\mathbf s(1),\dots$ be $n\times p$ matrices. If $\|\mathbf s\|_F^\lambda=\sup_{k\ge0}\lambda^{-k}\|\mathbf s(k)\|_F\le U$, then
--   $$\|\mathbf s(k)\|_F\le U\lambda^k\qquad\text{for all }k,$$
--   so $\|\mathbf s(k)\|_F$ converges to $0$ at a global R-linear (geometric) rate $O(\lambda^k)$.
--
--   This turns the bound produced by the small gain theorem into the convergence rate claimed in Theorem 10.
--
--   **Formalization Note.** The bound on the supremum is stated pointwise in $k$.
-- source:
--   Nedić, Olshevsky & Shi, arXiv:1607.03218v3, Lemma 4, p. 9

import Mathlib
import Definitions.Def_DIGing_Undir_Common

namespace DIGing.Undir

theorem lemma_4 {n p : ℕ} (s : ℕ → Stack n p) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (U : ℝ) (hU : ∀ k : ℕ, frob (s k) / lam ^ k ≤ U) :
    ∀ k : ℕ, frob (s k) ≤ U * lam ^ k := by sorry

end DIGing.Undir
