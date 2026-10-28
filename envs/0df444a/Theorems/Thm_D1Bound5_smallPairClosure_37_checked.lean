-- Prove2me | Theorems.Thm_D1Bound5_smallPairClosure_37_checked
-- name    : D1Bound5.smallPairClosure_37_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:22:57.81186+00:00
-- url     : https://prove2.me/theorems/a9239d8f-719f-4b2f-a8c4-c8896b4e50ed
-- title:
--   Small Pair Closure 37 checked
-- statement:
--   Auxiliary result `smallPairClosure_37_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure37.lean, lines 132-136, SHA-256 22f56e380519bc3957a3254f19fade940b347c7f1e2a204e28d8901e2f0cc0c0. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs37_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs37_Definitions_002

section
set_option autoImplicit false

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared37



theorem _root_.D1Bound5.smallPairClosure_37_checked :
    pairClosureBool smallPairA_37 smallPairB_37
      (10^1100) smallPairClosure_37 = true := by sorry

end D1Bound5
end
