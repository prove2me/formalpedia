-- Prove2me | Theorems.Thm_D1Bound5_product_neg_one_norms
-- name    : D1Bound5.product_neg_one_norms
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:53:44.32376+00:00
-- url     : https://prove2.me/theorems/c2f251cc-6078-44c5-ac4c-f33fb9e427c3
-- title:
--   Product neg one norms
-- statement:
--   Product minus one forces both positive integral norms to be one.
-- source:
--   D1Bound5/DegeneratePairClassification.lean, lines 10-32, SHA-256 61da8c7aa871a81d9d56989ed28825c79c1cef687d7de61a56038260054cdd37. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
namespace D1Bound5
open QuadInt




theorem _root_.D1Bound5.product_neg_one_norms {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b : QuadInt tau nu)
    (hprod : a*b+1=0) : a.norm=1 ∧ b.norm=1 := by sorry













end D1Bound5
end
