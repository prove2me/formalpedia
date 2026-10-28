-- Prove2me | Theorems.Thm_D1Bound5_degenerate_pair_model
-- name    : D1Bound5.degenerate_pair_model
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:51:30.828128+00:00
-- url     : https://prove2.me/theorems/0710c9b3-1215-4a20-8011-90944c924f8a
-- title:
--   Degenerate pair model
-- statement:
--   The only possible nonrational distinct product-minus-one pair lies in the Eisenstein model. No smallness hypothesis is needed.
-- source:
--   D1Bound5/DegeneratePairClassification.lean, lines 48-88, SHA-256 61da8c7aa871a81d9d56989ed28825c79c1cef687d7de61a56038260054cdd37. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_DegeneratePairClassification_Definitions

section
namespace D1Bound5
open QuadInt










theorem _root_.D1Bound5.degenerate_pair_model {tau nu : ℤ}
    (htau : tau=0 ∨ tau=1) (hd : 0 < discriminant tau nu)
    (a b : QuadInt tau nu) (hne : a ≠ b) (hprod : a*b+1=0) :
    RationalUnitPair a b ∨ (tau=1 ∧ nu=1) := by sorry







end D1Bound5
end
