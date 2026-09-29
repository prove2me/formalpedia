-- Prove2me | Theorems.Thm_ArithmeticE_polynomial_derivative_frame_minimal_equation
-- name    : ArithmeticE.polynomial_derivative_frame_minimal_equation
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-12T17:33:54.525047+00:00
-- url     : https://prove2.me/theorems/5b179af0-7468-4bec-9a59-dd6806600d8d
-- title:
--   A regular derivative-coordinate matrix yields a minimal scalar equation
-- statement:
--   Let $F\in\mathbb C[[X]]$, $\xi\in\mathbb C$, and $n\ge0$. Suppose $F$ has a polynomial derivative frame of order $n$: there are polynomially independent series $g_j$ and polynomial data $d,A,b$ with
--
--   $$dF^{(i)}=\sum_j A_{ij}g_j\quad(i<n),\qquad dF^{(n)}=\sum_j b_jg_j,$$
--
--   and $d(\xi)(\det A)(\xi)\ne0$. Then there are polynomials $p_k$ such that
--
--   $$\sum_{k=0}^n p_kF^{(k)}=0,\qquad p_n(\xi)\ne0,$$
--
--   and no nonzero polynomial differential operator of order less than $n$ annihilates $F$.
--
--   Thus the equation has minimal order and is ordinary at $\xi$. This is a purely algebraic implication; it has no E-function or arithmetic hypothesis. Order zero is allowed and corresponds to the frame forcing $F=0$.
-- source:
--   Auxiliary formalization of Beukers, A refined version of the Siegel–Shidlovskii theorem, Theorem 3.2, printed pp. 6–7 (prescribed derivative rows and determinant equation), https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf. These explicit polynomial-numerator and module-coordinate interfaces are derived from the proof, not quoted named lemmas.

import Definitions.Def_polynomialDerivativeFrame
open ArithmeticE

theorem ArithmeticE.polynomial_derivative_frame_minimal_equation
    (F : PowerSeries ℂ) (ξ : ℂ) (n : ℕ)
    (hf : PolynomialDerivativeFrame F ξ n) :
    ∃ p : ℕ → Polynomial ℂ, MinimalEquation p n F ∧ (p n).eval ξ ≠ 0 := by sorry
