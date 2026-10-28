-- Prove2me | Theorems.Thm_D1Bound5_fixed_cutoff_window_overlaps
-- name    : D1Bound5.fixed_cutoff_window_overlaps
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:46:55.258835+00:00
-- url     : https://prove2.me/theorems/f9069f6b-762d-47c0-9a85-f7831cbe6046
-- title:
--   Fixed cutoff window overlaps
-- statement:
--   Every adjacent fixed-table window overlaps for all fourth moduli at or beyond its certified cutoff. The actual analytic exclusions are supplied separately when this scalar theorem is applied to a tuple.
-- source:
--   D1Bound5/OneSmallFixedWindows.lean, lines 29-257, SHA-256 a89b44c2f3bb4ff79203e5d94458daa63b872e293c34f760393d0338cb4694eb. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_AllLargeWindows_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallFixedWindows_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_OrdinaryClosedIntervals_Definitions

section
namespace D1Bound5












theorem _root_.D1Bound5.fixed_cutoff_window_overlaps (r : OneSmallCutoffRow) (hr : r ∈ oneSmallCutoffRows)
    (B S T C : ℝ) (hB : 0 < B) (hS : 0 < S) (hT : 0 < T)
    (hBsq : B^2 = (r.b0 : ℝ)) (hSsq : S^2 = (r.s0 : ℝ))
    (hlarge : (r.triple.cutoff : ℝ) ≤ T^2)
    (hgap : (r.retainedCoefficient : ℝ)*T^5/S^2 < C) :
    (fixedWindowN2 r B C).1 < (allLargeWindowQ 1 T C).2 ∧
    (fixedWindowP r B S C).1 < (fixedWindowN2 r B C).2 ∧
    (fixedWindowA3 r B C).1 < (fixedWindowP r B S C).2 ∧
    (allLargeWindowM 1 B S C).1 < (fixedWindowA3 r B C).2 ∧
    (fixedWindowN3 r B C).1 < (allLargeWindowM 1 B S C).2 ∧
    (fixedWindowN3bs r B S C).1 < (fixedWindowN3 r B C).2 ∧
    (fixedWindowA4 r B C).1 < (fixedWindowN3bs r B S C).2 ∧
    ordinaryWindowLower B C 4 < (fixedWindowA4 r B C).2 ∧
    (fixedWindowA5 r B C).1 < ordinaryWindowUpper 1 B C 4 ∧
    ordinaryWindowLower B C 5 < (fixedWindowA5 r B C).2 ∧
    ordinaryWindowLower B C 6 < ordinaryWindowUpper 1 B C 5 ∧
    42*B^3*C < 2*C^2/(5*B) := by sorry

end D1Bound5
end
