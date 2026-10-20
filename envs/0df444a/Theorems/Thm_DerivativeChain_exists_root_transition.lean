-- Prove2me | Theorems.Thm_DerivativeChain_exists_root_transition
-- name    : DerivativeChain.exists_root_transition
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-17T18:37:39.882918+00:00
-- url     : https://prove2.me/theorems/2456e536-1824-48c6-b3d3-a636a96c3ab1
-- title:
--   Actual polynomial root transition
-- statement:
--   Let P be a complex polynomial of positive degree, and let z be a zero of its derivative. There is a finite probability distribution pi on the distinct roots w of P, with nonnegative real weights summing to one, whose real and imaginary weighted means equal those of z. Every supported index is an actual root of P. Multiplicity is incorporated in the weight construction, and shared roots are included.
--
--   $$\sum_w\pi_w\operatorname{Re}(w)=\operatorname{Re}(z),\qquad \sum_w\pi_w\operatorname{Im}(w)=\operatorname{Im}(z).$$
--
--   This supplies the actual-polynomial input required by abstract barycentric predecessor lemmas.
-- source:
--   Derivative-zero chains: public formalization reference, R13, DerivativeChain.exists_root_transition. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Definitions.Def_DerivativeChain_root_probability
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open scoped BigOperators Polynomial
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
open DerivativeChain

theorem DerivativeChain.exists_root_transition {P : ℂ[X]} {z : ℂ}
    (hP : 0 < P.degree) (hz : P.derivative.eval z = 0) :
    ∃ π : P.roots.toFinset → ℝ,
      (∀ w, 0 ≤ π w) ∧
      (∑ w, π w = 1) ∧
      (∑ w, π w * (w : ℂ).re = z.re) ∧
      (∑ w, π w * (w : ℂ).im = z.im) ∧
      (∀ w : P.roots.toFinset, P.eval (w : ℂ) = 0) := by sorry
