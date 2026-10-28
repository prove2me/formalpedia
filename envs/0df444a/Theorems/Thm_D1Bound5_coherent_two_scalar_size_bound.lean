-- Prove2me | Theorems.Thm_D1Bound5_coherent_two_scalar_size_bound
-- name    : D1Bound5.coherent_two_scalar_size_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:50.123921+00:00
-- url     : https://prove2.me/theorems/d881cb24-0179-47a2-b49f-67c2693f0aea
-- title:
--   Coherent two scalar size bound
-- statement:
--   A denominator-free numerical estimate underlying the two-anchor nonvanishing argument. The safe bound `5/4` on the scaled product of three roots is slightly weaker than its exact square-root value, but still gives the manuscript's strict constant five.
-- source:
--   D1Bound5/CoherentTwoSize.lean, lines 10-62, SHA-256 8a8f6db3352296dc34c3bf72970d3d3c0c58939fc28136095cce2e2e458acdfa. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.coherent_two_scalar_size_bound
    (A B P U Q : ℝ)
    (hA : 1 ≤ A) (hB : 3 ≤ B) (hP : 5 * B ≤ P) (hU0 : 0 ≤ U)
    (hU : U ^ 2 ≤ (A * B + 1) * (A * P + 1) * (B * P + 1))
    (hQ : Q ≤ A + B + P + 2 * A * B * P + 2 * U) :
    Q < 5 * A * B * P := by sorry









end D1Bound5
end
