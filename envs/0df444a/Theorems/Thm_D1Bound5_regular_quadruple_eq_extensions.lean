-- Prove2me | Theorems.Thm_D1Bound5_regular_quadruple_eq_extensions
-- name    : D1Bound5.regular_quadruple_eq_extensions
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:14.603995+00:00
-- url     : https://prove2.me/theorems/9e005058-cc38-4912-b402-c94578f4a7aa
-- title:
--   Regular quadruple eq extensions
-- statement:
--   The regular equation gives the usual two algebraic extensions of a triple. No division or nonzero-square-root hypothesis is used.
-- source:
--   D1Bound5/CoherentTwoSize.lean, lines 64-82, SHA-256 8a8f6db3352296dc34c3bf72970d3d3c0c58939fc28136095cce2e2e458acdfa. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.regular_quadruple_eq_extensions
    {F : Type*} [Field F] (a b p q r s t : F)
    (hr : r ^ 2 = a * b + 1) (hs : s ^ 2 = a * p + 1)
    (ht : t ^ 2 = b * p + 1)
    (hreg : (a + b - p - q) ^ 2 = 4 * (a * b + 1) * (p * q + 1)) :
    q = a + b + p + 2 * a * b * p + 2 * (r * s * t) ∨
    q = a + b + p + 2 * a * b * p - 2 * (r * s * t) := by sorry







end D1Bound5
end
