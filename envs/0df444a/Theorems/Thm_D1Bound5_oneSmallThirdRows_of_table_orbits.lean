-- Prove2me | Theorems.Thm_D1Bound5_oneSmallThirdRows_of_table_orbits
-- name    : D1Bound5.oneSmallThirdRows_of_table_orbits
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:28:22.929797+00:00
-- url     : https://prove2.me/theorems/36886c10-2f35-4eb5-9807-624ba1ab4cd8
-- title:
--   One Small Third Rows of table orbits
-- statement:
--   The fixed pair representatives classify third entries after one common normalization, preserving all equal-modulus cases and all square conditions.
-- source:
--   D1Bound5/OneSmallSymmetry.lean, lines 74-110, SHA-256 5e7e3f65dba87e2dd4102a7d04f343cef185fdf9cab42f19077c0873af7b7347. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FirstPairData_Definitions
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_OneSmallSymmetry_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions

section
namespace D1Bound5
open QuadInt














theorem _root_.D1Bound5.oneSmallThirdRows_of_table_orbits {tau nu : ℤ}
    (table : List ((ℤ × ℤ) × (ℤ × ℤ)))
    (reps : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (horbits : table.toFinset = reps.biUnion (firstPairOrbit tau))
    (hreps : ∀ row ∈ reps,
      OneSmallThirdRowProperty (firstPairRowA tau nu row) (firstPairRowB tau nu row))
    (a b s : QuadInt tau nu) (hrow : firstPairCoordinates a b ∈ table)
    (hbound : s.norm ≤ 224) (horder : b.norm ≤ s.norm)
    (ha : s ≠ a) (hb : s ≠ b) (hpair : PairExtension a b s) :
    OneSmallNormalizedThirdRows a b s := by sorry

end D1Bound5
end
