-- Prove2me | Theorems.Thm_D1Bound5_smallPairFilter_22_checked
-- name    : D1Bound5.smallPairFilter_22_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:10.996647+00:00
-- url     : https://prove2.me/theorems/5277f11e-e6fa-431d-a413-3d68caadeee9
-- title:
--   Small Pair Filter 22 checked
-- statement:
--   Auxiliary result `smallPairFilter_22_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic22.lean, lines 14-16, SHA-256 adb0922d008fd88dc4e6c502403fa271eff76e18e3492f2421c3a144fe6a9dcf. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs22_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs22_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphInputs22_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.smallPairFilter_22_checked :
    largePairVertices smallPairA_22 smallPairB_22 smallPairClosure_22 = smallPairLarge_22 := by sorry



end D1Bound5
end
