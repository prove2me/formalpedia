-- Prove2me | Theorems.Thm_D1Bound5_all_large_window_overlaps
-- name    : D1Bound5.all_large_window_overlaps
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:53:29.089229+00:00
-- url     : https://prove2.me/theorems/9ca37e9f-d584-490b-95f9-1c9df158bfe9
-- title:
--   All large window overlaps
-- statement:
--   All actual endpoint overlaps in the all-large branch, including both optional detours. The finite families are numerical expressions here; the final theorem supplies their genuine full-ring exclusions.
-- source:
--   D1Bound5/AllLargeWindowOverlaps.lean, lines 6-418, SHA-256 8d292ff181c6f66b2015dfc3cb5b2d8c48d6e1b5277846a32d41c8ee5328e48f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_AllLargeWindows_Definitions
import Definitions.Def_D1Bound5_OrdinaryClosedIntervals_Definitions

section
namespace D1Bound5


theorem _root_.D1Bound5.all_large_window_overlaps
    (A B S T C : ℝ) (hA : 3 ≤ A) (hAB : A ≤ B) (hBS : B ≤ S)
    (hT : 2*B*S < T) (hC : A^2*T^5/S^2 < C)
    (hgap : 400*(A^7*B^5*S^3) < C) :
    (allLargeWindowQ A T C).1 < A^2*C^7/(S^2*T^4) ∧
    (allLargeWindowN2 A B C).1 < (allLargeWindowQ A T C).2 ∧
    (allLargeWindowP A B S C).1 < (allLargeWindowN2 A B C).2 ∧
    (B^2 ≤ S → (allLargeWindowN3 A B C).1 < (allLargeWindowP A B S C).2) ∧
    (allLargeWindowA3 A B C).1 < (allLargeWindowP A B S C).2 ∧
    (S ≤ B^2 → (allLargeWindowM A B S C).1 < (allLargeWindowA3 A B C).2) ∧
    (allLargeWindowN3 A B C).1 < (allLargeWindowM A B S C).2 ∧
    (B^3 ≤ S → (allLargeWindowA4 A B C).1 < (allLargeWindowN3 A B C).2) ∧
    (S ≤ B^3 → (allLargeWindowN3 B S C).1 < (allLargeWindowN3 A B C).2) ∧
    (allLargeWindowA4 A B C).1 < (allLargeWindowN3 B S C).2 ∧
    ordinaryWindowLower B C 4 < (allLargeWindowA4 A B C).2 ∧
    (allLargeWindowA5 A B C).1 < ordinaryWindowUpper A B C 4 ∧
    ordinaryWindowLower B C 5 < (allLargeWindowA5 A B C).2 ∧
    ordinaryWindowLower B C 6 < ordinaryWindowUpper A B C 5 ∧
    42*B^3*C < 2*A*C^2/(5*B) := by sorry

end D1Bound5
end
