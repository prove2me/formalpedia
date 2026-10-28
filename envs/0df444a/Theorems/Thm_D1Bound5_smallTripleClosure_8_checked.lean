-- Prove2me | Theorems.Thm_D1Bound5_smallTripleClosure_8_checked
-- name    : D1Bound5.smallTripleClosure_8_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:32:43.620402+00:00
-- url     : https://prove2.me/theorems/528ef3b5-dc1f-4e17-8e28-d186e723ccbb
-- title:
--   Small Triple Closure 8 checked
-- statement:
--   Auxiliary result `smallTripleClosure_8_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallTripleExtensionData8.lean, lines 81-84, SHA-256 89ae5eb015cc06ce9d904be1f305c074eb3cd3fb88b017eb23ad5593272ca11e. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData8_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000











theorem _root_.D1Bound5.smallTripleClosure_8_checked :
    pairClosureBool smallTripleAnchorA_8 smallTripleAnchorB_8
      (10^80) smallTriplePairClosure_8 = true := by sorry





end D1Bound5
end
