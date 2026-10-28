-- Prove2me | Theorems.Thm_D1Bound5_smallPairClosure_3_checked
-- name    : D1Bound5.smallPairClosure_3_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:58.880987+00:00
-- url     : https://prove2.me/theorems/55cc0153-b6d4-476e-9819-b92043136e5f
-- title:
--   Small Pair Closure 3 checked
-- statement:
--   Auxiliary result `smallPairClosure_3_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure3.lean, lines 111-115, SHA-256 6d15b89a2a116c6555da85d4cf9731182d4a4f7703df9c0da4d69aaff9714776. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs3_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs3_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared3



theorem _root_.D1Bound5.smallPairClosure_3_checked :
    pairClosureBool smallPairA_3 smallPairB_3
      (10^1100) smallPairClosure_3 = true := by sorry

end D1Bound5
end
