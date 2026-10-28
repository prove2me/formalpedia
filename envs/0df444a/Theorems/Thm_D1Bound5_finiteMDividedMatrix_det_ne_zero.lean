-- Prove2me | Theorems.Thm_D1Bound5_finiteMDividedMatrix_det_ne_zero
-- name    : D1Bound5.finiteMDividedMatrix_det_ne_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:27.377373+00:00
-- url     : https://prove2.me/theorems/b29c13c3-67a6-411e-8a04-da443d673080
-- title:
--   Finite MDivided Matrix det ne zero
-- statement:
--   Nonsingularity of the actual integer polynomial matrix is inherited from the proved arbitrary-order Bennett determinant.
-- source:
--   D1Bound5/FiniteMBennettIdentity.lean, lines 129-163, SHA-256 291fd6ba981541548cef4bed5210986ea71cc1c1e28ff467e85be78d671f7779. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions

section
open Finset Polynomial

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]
















theorem _root_.D1Bound5.finiteMDividedMatrix_det_ne_zero (a b s c : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s) :
    (finiteMDividedMatrix a b s c).det ≠ 0 := by sorry

end D1Bound5
end
