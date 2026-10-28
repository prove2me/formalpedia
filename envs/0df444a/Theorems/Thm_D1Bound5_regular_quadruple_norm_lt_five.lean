-- Prove2me | Theorems.Thm_D1Bound5_regular_quadruple_norm_lt_five
-- name    : D1Bound5.regular_quadruple_norm_lt_five
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:22:42.962988+00:00
-- url     : https://prove2.me/theorems/f15de43d-5e4c-486d-ab92-9fc7d55dcbc0
-- title:
--   Regular quadruple norm lt five
-- statement:
--   A regular complex quadruple with the size hypotheses used in the strong two-anchor lemma has `Q < 5 A B P`.
-- source:
--   D1Bound5/CoherentTwoSize.lean, lines 84-129, SHA-256 8a8f6db3352296dc34c3bf72970d3d3c0c58939fc28136095cce2e2e458acdfa. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5






theorem _root_.D1Bound5.regular_quadruple_norm_lt_five
    (a b p q r s t : ℂ)
    (hr : r ^ 2 = a * b + 1) (hs : s ^ 2 = a * p + 1)
    (ht : t ^ 2 = b * p + 1)
    (hreg : (a + b - p - q) ^ 2 = 4 * (a * b + 1) * (p * q + 1))
    (hA : 1 ≤ ‖a‖) (hB : 3 ≤ ‖b‖) (hP : 5 * ‖b‖ ≤ ‖p‖) :
    ‖q‖ < 5 * ‖a‖ * ‖b‖ * ‖p‖ := by sorry





end D1Bound5
end
