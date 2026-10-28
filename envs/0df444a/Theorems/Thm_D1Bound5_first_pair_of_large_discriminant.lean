-- Prove2me | Theorems.Thm_D1Bound5_first_pair_of_large_discriminant
-- name    : D1Bound5.first_pair_of_large_discriminant
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:11:40.739895+00:00
-- url     : https://prove2.me/theorems/4f43bbf4-b04d-4e60-8bf3-ec4c7977d6c6
-- title:
--   First pair of large discriminant
-- statement:
--   The only first pair in any coordinate order of discriminant above 32 is the rational pair (1,3), up to simultaneous sign.
-- source:
--   D1Bound5/FirstPairClassification.lean, lines 22-80, SHA-256 7439f45210b59f019ad649fd7de039e4dd3225058c8cf127213409e314835de7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions

section
open scoped NumberField Classical
open Module

namespace D1Bound5
open QuadInt






theorem _root_.D1Bound5.first_pair_of_large_discriminant {tau nu : ℤ}
    (hlarge : 32 < discriminant tau nu) (a b : QuadInt tau nu)
    (hnorm : FirstPairNorms a b) (hroot : ∃ q, q*q = a*b+1) :
    (a = 1 ∧ b = 3) ∨ (a = -1 ∧ b = -3) := by sorry



end D1Bound5
end
