-- Prove2me | Theorems.Thm_D1Bound5_firstPairClassified_of_checked
-- name    : D1Bound5.firstPairClassified_of_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:28.206798+00:00
-- url     : https://prove2.me/theorems/7b663d64-daec-4d27-b987-63dee9ac33b5
-- title:
--   First Pair Classified of checked
-- statement:
--   Auxiliary result `firstPairClassified_of_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/OneSmallFiniteCheck.lean, lines 76-105, SHA-256 071c08b2bdc31b423cf7fceaeeb7fd97f8c1844d2c362578eed3d43c62423b55. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions

section
namespace D1Bound5
open QuadInt













theorem _root_.D1Bound5.firstPairClassified_of_checked {tau nu : ℤ}
    (hd : 0 < discriminant tau nu)
    (small roots : List (QuadInt tau nu))
    (rows : List ((ℤ × ℤ) × (ℤ × ℤ)))
    (hsmall : ∀ a ∈ disk tau nu 8, a ∈ small)
    (hroots : ∀ q ∈ disk tau nu 8, q ∈ roots)
    (hcheck : firstPairClassifiedBool small roots rows = true)
    (a b : QuadInt tau nu) (hnorm : FirstPairNorms a b)
    (hroot : ∃ q, q*q = a*b+1) :
    (a = 1 ∧ b = 3) ∨ (a = -1 ∧ b = -3) ∨ firstPairCoordinates a b ∈ rows := by sorry









end D1Bound5
end
