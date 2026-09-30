-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_cg_terminates
-- name    : ConjGrad.ErrorDecrease.cg_terminates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:54:50.721664+00:00
-- url     : https://prove2.me/theorems/82746e9c-a928-44a0-a84e-ae08a7618665
-- title:
--   Theorems 4:2 and 5:2 — the cg-method reaches the solution $h$ in at most $n$ steps
-- statement:
--   Let $A$ be a real symmetric positive definite $n\times n$ matrix, let $k\in\mathbb{R}^n$, and let $h$ be the solution of $Ah=k$. Let $x_0,x_1,x_2,\dots$ be the estimates produced by the cg-method (5:1) from an arbitrary starting point $x_0$. Then there is an index $m$ with
--
--   $$
--   m\le n \quad\text{and}\quad x_m = h .
--   $$
--
--   This is Theorem 4:2 ("The cd-method is an $m$-step method ($m\le n$) in the sense that at the $m$th step the estimate $x_m$ is the desired solution $h$"), applied to the cg-method through Theorem 5:2 ("The cg-method is a cd-method"). It is the setting of Section 6 of the paper, "Let now $x_0,x_1,\dots,x_m=h$ be the estimates of $h$ obtained by applying the cg-method", and it is used in the proof of Theorem 6:3.
--
--   **Formalization Note** The cg sequence is the unguarded recursion of the definition, so after step $m$ it stays at $h$. Symmetry of $A$ is part of Mathlib's `Matrix.PosDef`.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), p. 412, Theorem 4:2, applied through p. 415, Theorem 5:2; setting of Section 6, p. 416

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter

open Matrix

namespace ConjGrad.ErrorDecrease

theorem cg_terminates {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) :
    ∃ m ≤ n, (cgIter A k x₀ m).x = h := by sorry

end ConjGrad.ErrorDecrease
