-- Prove2me | Theorems.Thm_D1Bound5_firstPairOrbit_normalize
-- name    : D1Bound5.firstPairOrbit_normalize
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:43:27.01814+00:00
-- url     : https://prove2.me/theorems/d6b54034-11ec-44e1-9f13-4b03fea7e358
-- title:
--   First Pair Orbit normalize
-- statement:
--   The ordered coordinate orbit admits actual involutive normalization.
-- source:
--   D1Bound5/OneSmallSymmetry.lean, lines 24-53, SHA-256 5e7e3f65dba87e2dd4102a7d04f343cef185fdf9cab42f19077c0873af7b7347. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions

section
namespace D1Bound5
open QuadInt








theorem _root_.D1Bound5.firstPairOrbit_normalize {tau nu : ℤ}
    (a b : QuadInt tau nu) (row : (ℤ × ℤ) × (ℤ × ℤ))
    (horbit : firstPairCoordinates a b ∈ firstPairOrbit tau row) :
    ∃ sgn conj : Bool,
      smallExtensionSymmetry sgn conj a = firstPairRowA tau nu row ∧
      smallExtensionSymmetry sgn conj b = firstPairRowB tau nu row := by sorry







end D1Bound5
end
