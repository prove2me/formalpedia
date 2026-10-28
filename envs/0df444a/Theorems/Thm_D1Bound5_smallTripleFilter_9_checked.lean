-- Prove2me | Theorems.Thm_D1Bound5_smallTripleFilter_9_checked
-- name    : D1Bound5.smallTripleFilter_9_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:35:00.184271+00:00
-- url     : https://prove2.me/theorems/5f97a13f-8a14-4b41-a01c-267c5a6526fb
-- title:
--   Small Triple Filter 9 checked
-- statement:
--   Auxiliary result `smallTripleFilter_9_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallTripleExtensionData9.lean, lines 112-115, SHA-256 d547b2c59760d0754a4660f0e6f6a2dd995b480c12bf4f53eac6fc574c6b3772. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData9_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000













theorem _root_.D1Bound5.smallTripleFilter_9_checked :
    tripleExtensionFilterBool smallTripleAnchorA_9 smallTripleAnchorB_9
      smallTripleAnchorC_9 smallTriplePairClosure_9 smallTripleAllowed_9 = true := by sorry



end D1Bound5
end
