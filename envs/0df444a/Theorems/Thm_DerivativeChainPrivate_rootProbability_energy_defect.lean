-- Prove2me | Theorems.Thm_DerivativeChainPrivate_rootProbability_energy_defect
-- name    : DerivativeChainPrivate.rootProbability_energy_defect
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-17T18:44:38.812978+00:00
-- url     : https://prove2.me/theorems/324283c5-c20a-4c74-b479-5659342f115d
-- title:
--   Zero mean of the polynomial energy defect
-- statement:
--   For a positive-degree complex polynomial P and a critical point z, the normalized actual-root probability law satisfies
--
--   $$\sum_w\pi_w\bigl(|w-z|^2-|w|^2+|z|^2\bigr)=0.$$
--
--   No disk or root-simplicity hypothesis is imposed. This identity provides a root with a nonpositive energy defect.
-- source:
--   Derivative-zero chains: public formalization reference, R23, DerivativeChainPrivate.rootProbability_energy_defect. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

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
namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate

theorem DerivativeChainPrivate.rootProbability_energy_defect (P : ℂ[X]) (hP : 0 < P.degree)
    (z : ℂ) (hz : P.derivative.eval z = 0) :
    (∑ w : P.roots.toFinset, DerivativeChain.rootProbability P z w *
      (‖(w : ℂ) - z‖ ^ 2 - ‖(w : ℂ)‖ ^ 2 + ‖z‖ ^ 2)) = 0 := by sorry
