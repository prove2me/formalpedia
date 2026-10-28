-- Prove2me | Theorems.Thm_D1Bound5_rationalCutoff_triple_norms
-- name    : D1Bound5.rationalCutoff_triple_norms
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:20:04.42991+00:00
-- url     : https://prove2.me/theorems/9640e909-3062-4240-be31-f40fbae0d671
-- title:
--   Rational Cutoff triple norms
-- statement:
--   The complete retained-start norm packet for the universal rational triple. Only the common sign is needed; integer anchors are fixed by conjugation.
-- source:
--   D1Bound5/RationalCutoffNorms.lean, lines 13-29, SHA-256 7e14b14398c156606f9521e6ae9c9db75e66fe50dedbdbd1984734965b9c2d93. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
open scoped NumberField

namespace D1Bound5







theorem _root_.D1Bound5.rationalCutoff_triple_norms
    {K : Type*} [Field K] [NumberField K] (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (sgn : Bool)
    (h0 : a 0 = if sgn then -1 else 1)
    (h1 : a 1 = if sgn then -3 else 3)
    (h2 : a 2 = if sgn then -8 else 8) :
    ‖phi (a 0 : K)‖^2 = (oneSmallCutoffRow_56.a0 : ℝ) ∧
    ‖phi (a 1 : K)‖^2 = (oneSmallCutoffRow_56.b0 : ℝ) ∧
    ‖phi (a 2 : K)‖^2 = (oneSmallCutoffRow_56.s0 : ℝ) ∧
    ‖phi (a 0 : K)-phi (a 1 : K)‖^2 = (oneSmallCutoffRow_56.dab : ℝ) ∧
    ‖phi (a 0 : K)-phi (a 2 : K)‖^2 = (oneSmallCutoffRow_56.das : ℝ) ∧
    ‖phi (a 1 : K)-phi (a 2 : K)‖^2 = (oneSmallCutoffRow_56.dbs : ℝ) := by sorry

end D1Bound5
end
