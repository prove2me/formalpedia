-- Prove2me | Theorems.Thm_D1Bound5_smallPairClosure_22_checked
-- name    : D1Bound5.smallPairClosure_22_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:34.231083+00:00
-- url     : https://prove2.me/theorems/86ca4eaa-2020-406c-8a6a-1f3273f2de52
-- title:
--   Small Pair Closure 22 checked
-- statement:
--   Auxiliary result `smallPairClosure_22_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure22.lean, lines 105-109, SHA-256 1ad5c144188014238a603cfc8b0bd2d1c22589652257fbede20b4eafce2a9f80. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs22_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs22_Definitions_002

section
set_option autoImplicit false

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared22



theorem _root_.D1Bound5.smallPairClosure_22_checked :
    pairClosureBool smallPairA_22 smallPairB_22
      (10^1100) smallPairClosure_22 = true := by sorry

end D1Bound5
end
