-- Prove2me | Theorems.Thm_DerivativeChain_rootProbability_centered_increment
-- name    : DerivativeChain.rootProbability_centered_increment
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-17T18:37:57.595962+00:00
-- url     : https://prove2.me/theorems/626fdc9d-810f-4cba-980a-1849dfedf1a7
-- title:
--   Centered increment of the polynomial root transition
-- statement:
--   Let P have positive degree, let P'(z)=0, and fix any complex reference point u. For the normalized Gauss--Lucas root weights pi on the actual roots w,
--
--   $$\sum_w\pi_w\bigl(\operatorname{Re}(z-u)\operatorname{Re}(w-z)+\operatorname{Im}(z-u)\operatorname{Im}(w-z)\bigr)=0.$$
--
--   There is no unit-disk assumption. This is a centered-increment identity for one actual derivative transition.
-- source:
--   Derivative-zero chains: public formalization reference, R14, DerivativeChain.rootProbability_centered_increment. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

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

theorem DerivativeChain.rootProbability_centered_increment {P : ℂ[X]} {z : ℂ}
    (hP : 0 < P.degree) (hz : P.derivative.eval z = 0) (u : ℂ) :
    (∑ w : P.roots.toFinset, rootProbability P z w *
      ((z - u).re * ((w : ℂ) - z).re +
        (z - u).im * ((w : ℂ) - z).im)) = 0 := by sorry
