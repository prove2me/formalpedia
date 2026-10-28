-- Prove2me | Theorems.Thm_D1Bound5_smallPairFilter_26_checked
-- name    : D1Bound5.smallPairFilter_26_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:00.864391+00:00
-- url     : https://prove2.me/theorems/7669f3e3-723e-44fb-acde-15405d7c49c8
-- title:
--   Small Pair Filter 26 checked
-- statement:
--   Auxiliary result `smallPairFilter_26_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic26.lean, lines 15-17, SHA-256 cbbc65cfed7a832ddfa9ca69b07879fe90037350ea43af08803d5f8876358fea. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.smallPairFilter_26_checked :
    largePairVertices smallPairA_26 smallPairB_26 smallPairClosure_26 = smallPairLarge_26 := by sorry



end D1Bound5
end
