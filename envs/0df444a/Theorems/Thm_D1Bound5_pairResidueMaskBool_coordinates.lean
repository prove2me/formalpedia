-- Prove2me | Theorems.Thm_D1Bound5_pairResidueMaskBool_coordinates
-- name    : D1Bound5.pairResidueMaskBool_coordinates
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:35:38.955979+00:00
-- url     : https://prove2.me/theorems/16b4f910-e61a-46e2-83b1-b4f93464c369
-- title:
--   Pair Residue Mask Bool coordinates
-- statement:
--   This is equality of the actual computational mask predicates; no primality, mask-validity, nonzero, or square-root assumption is used.
-- source:
--   D1Bound5/PairCachedResidues.lean, lines 21-31, SHA-256 8d30539028d401e948637a33f705cb33707d8ad4e1fe939eafd5ed7c690a9100. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions

section
namespace D1Bound5






theorem _root_.D1Bound5.pairResidueMaskBool_coordinates {tau nu : ℤ} (k mask : ℕ)
    (x y : QuadInt tau nu) :
    pairResidueMaskBool tau nu k mask (pairCoordinateResidues k x)
      (pairCoordinateResidues k y) = coordinateSquareMaskBool k mask (x * y + 1) := by sorry





















end D1Bound5
end
