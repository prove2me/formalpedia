-- Prove2me | Theorems.Thm_D1Bound5_unit_pair_pell_parameter_parity
-- name    : D1Bound5.unit_pair_pell_parameter_parity
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:33:23.287135+00:00
-- url     : https://prove2.me/theorems/2d612b1b-56de-40b0-bb87-01ebed773327
-- title:
--   Unit pair pell parameter parity
-- statement:
--   A norm-two Pell solution has one of precisely the two relevant parameter congruences. No primitivity or positive-root assumption is used.
-- source:
--   D1Bound5/UnitPairPellParity.lean, lines 15-25, SHA-256 c3ad7f99dff414563641d91e1befe6673fc12f66d324008fa09e8f3018431ad6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped NumberField
open Module

namespace D1Bound5




theorem _root_.D1Bound5.unit_pair_pell_parameter_parity (d u v : ℤ)
    (h : u ^ 2 - d * v ^ 2 = 2) : d % 8 = 7 ∨ d % 4 = 2 := by sorry







end D1Bound5
end
