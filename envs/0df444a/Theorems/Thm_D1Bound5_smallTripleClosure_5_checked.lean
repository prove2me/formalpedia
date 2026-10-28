-- Prove2me | Theorems.Thm_D1Bound5_smallTripleClosure_5_checked
-- name    : D1Bound5.smallTripleClosure_5_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:39:17.438515+00:00
-- url     : https://prove2.me/theorems/d4249d5a-0936-4e20-a6bf-67b98736875b
-- title:
--   Small Triple Closure 5 checked
-- statement:
--   Auxiliary result `smallTripleClosure_5_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallTripleExtensionData5.lean, lines 95-98, SHA-256 0f52c03dcb1aef0af13ae431869add34d508399252e4add0eccf7dd09dc092de. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SmallTripleExtensionData5_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000











theorem _root_.D1Bound5.smallTripleClosure_5_checked :
    pairClosureBool smallTripleAnchorA_5 smallTripleAnchorB_5
      (10^80) smallTriplePairClosure_5 = true := by sorry





end D1Bound5
end
