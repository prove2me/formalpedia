-- Prove2me | Theorems.Thm_D1Bound5_smallPairClosure_15_checked
-- name    : D1Bound5.smallPairClosure_15_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:22.914215+00:00
-- url     : https://prove2.me/theorems/9975313a-05a3-46b9-848a-1359af54d3c2
-- title:
--   Small Pair Closure 15 checked
-- statement:
--   Auxiliary result `smallPairClosure_15_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure15.lean, lines 13-17, SHA-256 5baf164a0b774bed7f5683380949ad05bab57d90453328daacdf3f288dc47924. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Algebra.Order.Ring.Abs
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
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs15_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs15_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared15



theorem _root_.D1Bound5.smallPairClosure_15_checked :
    pairClosureBool smallPairA_15 smallPairB_15
      (10^1100) smallPairClosure_15 = true := by sorry

end D1Bound5
end
