-- Prove2me | Theorems.Thm_ArithmeticE_cleared_derivative_jet_interpolation
-- name    : ArithmeticE.cleared_derivative_jet_interpolation
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-12T17:34:56.951587+00:00
-- url     : https://prove2.me/theorems/9fb952b4-cc1c-4511-a132-a8aee9b25b4c
-- title:
--   Algebraic polynomial interpolation of cleared derivative rows
-- statement:
--   Let $T\in\mathbb Q[X]$ and let $B$ be an $m\times m$ rational polynomial matrix. Fix an algebraic complex number $\xi$ with $T(\xi)\ne0$. For any $N\ge0$ and any prescribed algebraic rows $w_0,\ldots,w_{N-1}\in\overline{\mathbb Q}^{\,m}$, there is a row $P$ of polynomials with algebraic coefficients such that
--
--   $$R_k(P)(\xi)=w_k\qquad(0\le k<N),$$
--
--   where $R_0(P)=P$ and $R_{k+1}(P)=TR_k(P)'+R_k(P)B-kT'R_k(P)$.
--
--   This is the finite interpolation component of the ordinary cyclic-vector construction. It involves no E-functions, convergence, or arithmetic denominator estimates. The cases $N=0$ and $m=0$ are included.
-- source:
--   Auxiliary formalization of Beukers, A refined version of the Siegel–Shidlovskii theorem, Theorem 3.2, printed pp. 6–7 (prescribed derivative rows and determinant equation), https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf. These explicit polynomial-numerator and module-coordinate interfaces are derived from the proof, not quoted named lemmas.

import Definitions.Def_clearedDerivativeRows
open ArithmeticE

theorem ArithmeticE.cleared_derivative_jet_interpolation
    (m : ℕ) (T : Polynomial ℚ) (B : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (ξ : ℂ) (hξ : IsAlgebraic ℚ ξ)
    (hreg : T.eval₂ (algebraMap ℚ ℂ) ξ ≠ 0)
    (N : ℕ) (w : ℕ → Fin m → ℂ)
    (hw : ∀ k < N, ∀ i, IsAlgebraic ℚ (w k i)) :
    ∃ P : Fin m → Polynomial ℂ,
      (∀ i k, IsAlgebraic ℚ ((P i).coeff k)) ∧
      ∀ k < N, ∀ i, (clearedDerivativeRows T B P k i).eval ξ = w k i := by sorry
