-- Prove2me | Theorems.Thm_D1Bound5_smallPairClosure_31_checked
-- name    : D1Bound5.smallPairClosure_31_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:36.763592+00:00
-- url     : https://prove2.me/theorems/a899f754-a0b3-436e-95bd-aec3170614bf
-- title:
--   Small Pair Closure 31 checked
-- statement:
--   Auxiliary result `smallPairClosure_31_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure31.lean, lines 15-19, SHA-256 158ad2bc2984a2c5ba3dac1285f2ee71d25d8138367e6f04ba67264e3cc71dca. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs31_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared31



theorem _root_.D1Bound5.smallPairClosure_31_checked :
    pairClosureBool smallPairA_31 smallPairB_31
      (10^1100) smallPairClosure_31 = true := by sorry

end D1Bound5
end
