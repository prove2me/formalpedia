-- Prove2me | Theorems.Thm_D1Bound5_smallPairClosure_32_checked
-- name    : D1Bound5.smallPairClosure_32_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:50:09.178118+00:00
-- url     : https://prove2.me/theorems/5c51341a-b7f6-41b6-8a06-2550be2bbdf8
-- title:
--   Small Pair Closure 32 checked
-- statement:
--   Auxiliary result `smallPairClosure_32_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure32.lean, lines 15-19, SHA-256 d81733301ce0970cad0d6399ce480fe28c4050506f7914c71497601099e30860. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs32_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared32



theorem _root_.D1Bound5.smallPairClosure_32_checked :
    pairClosureBool smallPairA_32 smallPairB_32
      (10^1100) smallPairClosure_32 = true := by sorry

end D1Bound5
end
