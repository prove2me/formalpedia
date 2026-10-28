-- Prove2me | Theorems.Thm_D1Bound5_gaussian_degenerate_pair
-- name    : D1Bound5.gaussian_degenerate_pair
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:52:05.280734+00:00
-- url     : https://prove2.me/theorems/0443bbcd-e580-4b1b-90ff-74f7fd07d3d3
-- title:
--   Gaussian degenerate pair
-- statement:
--   Distinct Gaussian units with product minus one are exactly {-1,1}. The apparent Gaussian alternatives ±i would repeat the same entry.
-- source:
--   D1Bound5/DegeneratePairClassification.lean, lines 40-46, SHA-256 61da8c7aa871a81d9d56989ed28825c79c1cef687d7de61a56038260054cdd37. Project: https://github.com/tomislav-math/d1-bound5-lean

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








theorem _root_.D1Bound5.gaussian_degenerate_pair (a b : QuadInt 0 1) (hne : a ≠ b)
    (hprod : a*b+1=0) : RationalUnitPair a b := by sorry









end D1Bound5
end
