-- Prove2me | Theorems.Thm_D1Bound5_coherent_two_three_forms_not_both_zero
-- name    : D1Bound5.coherent_two_three_forms_not_both_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:28:49.785602+00:00
-- url     : https://prove2.me/theorems/638f3cea-fc0f-4187-a3ff-eb49e4821ac7
-- title:
--   Coherent two three forms not both zero
-- statement:
--   The two coherent polynomial-weight forms cannot both vanish under the four-anchor size condition. Arbitrary square-root signs are allowed, provided the two forms use the same roots on their overlap.
-- source:
--   D1Bound5/CoherentThreeNonvanishing.lean, lines 129-163, SHA-256 20f76d470fd8a77be69b6cbe7c960d5062bc8bb2410754eb1f27bcf0090be809. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open Finset

namespace D1Bound5








theorem _root_.D1Bound5.coherent_two_three_forms_not_both_zero
    (a R : Fin 4 → ℂ) (hinj : Function.Injective a) (p q z : ℂ)
    (hz : z^2 = p*q+1) (hR : ∀ i, (R i)^2 = (a i*p+1)*(a i*q+1))
    (hA : 1 ≤ ‖a 0‖) (hAB : ‖a 0‖ ≤ ‖a 1‖)
    (hBS : ‖a 1‖ ≤ ‖a 2‖) (hST : ‖a 2‖ ≤ ‖a 3‖)
    (hTP : ‖a 3‖ ≤ ‖p‖) (hPQ : ‖p‖ ≤ ‖q‖)
    (hsize : 32*‖a 1‖*‖a 2‖*‖a 3‖/‖a 0‖^3 ≤ ‖p‖^2) :
    (-(a 0-a 1)*(a 0-a 2)*(a 1-a 2)*z +
      a 0*(a 1-a 2)*R 0 - a 1*(a 0-a 2)*R 1 + a 2*(a 0-a 1)*R 2 ≠ 0) ∨
    (-(a 0-a 1)*(a 0-a 3)*(a 1-a 3)*z +
      a 0*(a 1-a 3)*R 0 - a 1*(a 0-a 3)*R 1 + a 3*(a 0-a 1)*R 3 ≠ 0) := by sorry







end D1Bound5
end
