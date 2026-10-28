-- Prove2me | Theorems.Thm_D1Bound5_smallPairFilter_29_checked
-- name    : D1Bound5.smallPairFilter_29_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:30:24.374146+00:00
-- url     : https://prove2.me/theorems/1bae30b7-03da-4b12-a785-ca7a6b810afa
-- title:
--   Small Pair Filter 29 checked
-- statement:
--   Auxiliary result `smallPairFilter_29_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic29.lean, lines 13-15, SHA-256 9c03dd78331bb1db2c0289b5b4d68f04d20fe5e7fa15fee676c238927f047874. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs29_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs29_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphInputs29_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.smallPairFilter_29_checked :
    largePairVertices smallPairA_29 smallPairB_29 smallPairClosure_29 = smallPairLarge_29 := by sorry



end D1Bound5
end
