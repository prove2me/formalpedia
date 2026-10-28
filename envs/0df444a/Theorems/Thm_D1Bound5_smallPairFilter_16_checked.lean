-- Prove2me | Theorems.Thm_D1Bound5_smallPairFilter_16_checked
-- name    : D1Bound5.smallPairFilter_16_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:10.061984+00:00
-- url     : https://prove2.me/theorems/f10065bd-caa9-4301-91d6-2f193bd9cee5
-- title:
--   Small Pair Filter 16 checked
-- statement:
--   Auxiliary result `smallPairFilter_16_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic16.lean, lines 13-15, SHA-256 bd98f697bcf6d72c3084f4bb93b5d03975a38ffeff8bbcce40f798c8c7e817f6. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs16_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs16_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.smallPairFilter_16_checked :
    largePairVertices smallPairA_16 smallPairB_16 smallPairClosure_16 = smallPairLarge_16 := by sorry



end D1Bound5
end
