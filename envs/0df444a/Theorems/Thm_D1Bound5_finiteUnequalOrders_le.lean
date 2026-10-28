-- Prove2me | Theorems.Thm_D1Bound5_finiteUnequalOrders_le
-- name    : D1Bound5.finiteUnequalOrders_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:38.87598+00:00
-- url     : https://prove2.me/theorems/53c27b6f-82e3-4d7b-9654-3e3f20885e88
-- title:
--   Finite Unequal Orders le
-- statement:
--   Auxiliary result `finiteUnequalOrders_le` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteUnequalEntry.lean, lines 21-23, SHA-256 4a25eb90becd225388fecc7352da19731da09bdef68e85c87dced6c4c45eeb61. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteUnequalEntry_Definitions

section
open Finset

namespace D1Bound5





theorem _root_.D1Bound5.finiteUnequalOrders_le (k m : ℕ) (hmk : m ≤ k) (i j : Fin 3) :
    finiteUnequalOrders k m i j ≤ k := by sorry



variable {F : Type*} [Field F] [CharZero F]















end D1Bound5
end
