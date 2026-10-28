-- Prove2me | Theorems.Thm_D1Bound5_finiteUnequalClearedEntry_residual_norm_le
-- name    : D1Bound5.finiteUnequalClearedEntry_residual_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:31:43.88417+00:00
-- url     : https://prove2.me/theorems/1712205b-6dca-49d0-923d-e61006ebae10
-- title:
--   Finite Unequal Cleared Entry residual norm le
-- statement:
--   Actual unequal-pole residual bound after clearing. The binomial factor and tail degree remain exact, allowing the finite A3/A4/A5 constants to be evaluated independently with rational arithmetic.
-- source:
--   D1Bound5/FiniteUnequalEntry.lean, lines 89-159, SHA-256 4a25eb90becd225388fecc7352da19731da09bdef68e85c87dced6c4c45eeb61. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Definitions.Def_D1Bound5_FiniteUnequalEntry_Definitions

section
open Finset

namespace D1Bound5









variable {F : Type*} [Field F] [CharZero F]














theorem _root_.D1Bound5.finiteUnequalClearedEntry_residual_norm_le
    (x y c : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y)
    (hXY : ‖x‖ ≤ ‖y‖) (hXC : 1 < ‖x‖*‖c‖)
    (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k)
    (hs : (k : ℝ)+1/2 < (m+2*k : ℕ)) (i : Fin 3) :
    ‖∑ j, finiteUnequalClearedEntry x y c k m i j*
        (1+bennettTwoNodes x y j*(x*y*c)⁻¹)^(1/2 : ℂ)‖ ≤
      (4^k*‖x-y‖^(2*k)/(‖x‖^k*‖y‖^k*‖c‖^(m+k)))*
        |Ring.choose ((k : ℝ)+1/2) (m+2*k)| /
          (1-1/(‖x‖*‖c‖))^(((m+2*k : ℕ) : ℝ)-((k : ℝ)+1/2)) := by sorry

end D1Bound5
end
