-- Prove2me | Theorems.Thm_BranchActualQ_nonnegative_unconditional
-- name    : BranchActualQ.nonnegative_unconditional
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-20T10:52:09.226772+00:00
-- url     : https://prove2.me/theorems/1609b895-8fb3-4e92-92a5-1e3bcea3252f
-- title:
--   Nonnegativity of the original xi-derived tower at all positive arguments
-- statement:
--   Let $G(x)$ be the real part of the completed xi function at $1/2+\sqrt{x}$, using the normalization in the formal statement. Its logarithmic derivatives define $Q_n(u)$. For every integer $n\ge 1$ and every real $u>0$, $$Q_n(u)\ge 0.$$ The result excludes a negative seed at the base of this tower.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandão Bueno. Composition of the closed finite-height verification with the original xi-based tower theorem.

import Mathlib

theorem BranchActualQ.nonnegative_unconditional :
    let f : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let G : ℝ → ℝ := fun x => (f (1/2+(Real.sqrt x : ℂ))).re
    let Q : ℕ → ℝ → ℝ := fun n u =>
      (2 : ℝ)^n*u^(2*n-1)*(-1 : ℝ)^(n-1)*
        iteratedDeriv n (fun x => Real.log (G x)-Real.log (G 0)) (u^2)
    ∀ (n : ℕ), 1 ≤ n → ∀ u > 0, 0 ≤ Q n u := by sorry
