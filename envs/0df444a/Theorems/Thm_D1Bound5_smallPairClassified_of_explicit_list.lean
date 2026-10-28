-- Prove2me | Theorems.Thm_D1Bound5_smallPairClassified_of_explicit_list
-- name    : D1Bound5.smallPairClassified_of_explicit_list
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:23:50.442512+00:00
-- url     : https://prove2.me/theorems/6e98c0e6-d48e-4d20-b336-d46c300ccdbe
-- title:
--   Small Pair Classified of explicit list
-- statement:
--   Auxiliary result `smallPairClassified_of_explicit_list` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairClassificationCheck.lean, lines 21-38, SHA-256 13b30ee79d1344410e8883c71036e3d9b17e9072cb676e51f16a84aa1a8cfd5a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
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
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_SmallPairClassificationCheck_Definitions

section
namespace D1Bound5
open QuadInt





theorem _root_.D1Bound5.smallPairClassified_of_explicit_list {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (xs : List (QuadInt tau nu))
    (rows : List (Finset (ℤ × ℤ)))
    (cover : ∀ z ∈ disk tau nu 8, z ∈ xs)
    (checked : smallPairClassifiedBool xs rows = true)
    (a b : QuadInt tau nu) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hroot : ∃ r, r*r = a*b+1) (hnondeg : a*b+1 ≠ 0)
    (hNa : a.norm ≤ 8) (hNb : b.norm ≤ 8) : pairCoordinates a b ∈ rows := by sorry

end D1Bound5
end
