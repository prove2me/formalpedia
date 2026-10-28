-- Prove2me | Theorems.Thm_D1Bound5_smallPairFilter_37_checked
-- name    : D1Bound5.smallPairFilter_37_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:31:03.427076+00:00
-- url     : https://prove2.me/theorems/9ccd5497-04ea-4efb-983e-b35b1496bf6e
-- title:
--   Small Pair Filter 37 checked
-- statement:
--   Auxiliary result `smallPairFilter_37_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic37.lean, lines 14-16, SHA-256 7261cda8270070eae87a83e46a05e8dfdd9d47ce64647c0cd5b58d0edc9f00a4. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs37_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs37_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphInputs37_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.smallPairFilter_37_checked :
    largePairVertices smallPairA_37 smallPairB_37 smallPairClosure_37 = smallPairLarge_37 := by sorry



end D1Bound5
end
