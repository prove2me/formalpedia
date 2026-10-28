-- Prove2me | Theorems.Thm_D1Bound5_smallPairFilter_19_checked
-- name    : D1Bound5.smallPairFilter_19_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:31:22.576959+00:00
-- url     : https://prove2.me/theorems/0b0d4f3a-822c-4f4e-967e-d1d064f01c5b
-- title:
--   Small Pair Filter 19 checked
-- statement:
--   Auxiliary result `smallPairFilter_19_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic19.lean, lines 13-15, SHA-256 3b56e51ec5eabd27d405632f3d20cd07766a573c3ca28f4252e17239730adc09. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs19_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs19_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphInputs19_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.smallPairFilter_19_checked :
    largePairVertices smallPairA_19 smallPairB_19 smallPairClosure_19 = smallPairLarge_19 := by sorry



end D1Bound5
end
