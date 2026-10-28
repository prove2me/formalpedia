-- Prove2me | Theorems.Thm_D1Bound5_smallPairClosure_7_checked
-- name    : D1Bound5.smallPairClosure_7_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:21.602138+00:00
-- url     : https://prove2.me/theorems/e1185246-ae23-4644-8705-b549adef48ea
-- title:
--   Small Pair Closure 7 checked
-- statement:
--   Auxiliary result `smallPairClosure_7_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure7.lean, lines 118-122, SHA-256 e1f13391e3d5584dde6e6e079e559609cf1729a21d7dd45c70ea502659435127. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs7_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs7_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared7



theorem _root_.D1Bound5.smallPairClosure_7_checked :
    pairClosureBool smallPairA_7 smallPairB_7
      (10^1100) smallPairClosure_7 = true := by sorry

end D1Bound5
end
