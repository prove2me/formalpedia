-- Prove2me | Theorems.Thm_D1Bound5_smallPairFilter_47_checked
-- name    : D1Bound5.smallPairFilter_47_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:29:54.084506+00:00
-- url     : https://prove2.me/theorems/a3c218fd-c173-494e-bc8e-ba18de8b3ab6
-- title:
--   Small Pair Filter 47 checked
-- statement:
--   Auxiliary result `smallPairFilter_47_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic47.lean, lines 13-15, SHA-256 33d28d1cdc773c8feaf8f5fa9085c4d1ab9e83a9f52e395db9c66a0df6c6682e. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Data.List.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs47_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs47_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.smallPairFilter_47_checked :
    largePairVertices smallPairA_47 smallPairB_47 smallPairClosure_47 = smallPairLarge_47 := by sorry



end D1Bound5
end
