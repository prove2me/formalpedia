-- Prove2me | Theorems.Thm_D1Bound5_smallPairFilter_43_checked
-- name    : D1Bound5.smallPairFilter_43_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:21.374443+00:00
-- url     : https://prove2.me/theorems/af6ae326-14fd-4162-929a-11c4361ea3bb
-- title:
--   Small Pair Filter 43 checked
-- statement:
--   Auxiliary result `smallPairFilter_43_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic43.lean, lines 13-15, SHA-256 e5f34b379ce5169c43ac116b737d74c40f2d6c8e9799f87b666db23e5ef5c3f2. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs43_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs43_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphInputs43_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.smallPairFilter_43_checked :
    largePairVertices smallPairA_43 smallPairB_43 smallPairClosure_43 = smallPairLarge_43 := by sorry



end D1Bound5
end
