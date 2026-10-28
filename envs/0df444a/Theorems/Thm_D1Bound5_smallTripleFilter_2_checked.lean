-- Prove2me | Theorems.Thm_D1Bound5_smallTripleFilter_2_checked
-- name    : D1Bound5.smallTripleFilter_2_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:33:47.254992+00:00
-- url     : https://prove2.me/theorems/4ea28053-d04a-4540-8dec-151cea866be4
-- title:
--   Small Triple Filter 2 checked
-- statement:
--   Auxiliary result `smallTripleFilter_2_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallTripleExtensionData2.lean, lines 118-121, SHA-256 66875e77685eb2e4ee8ce1ba4229501c18260c5f57e52d69ee57585e35929046. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData2_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000













theorem _root_.D1Bound5.smallTripleFilter_2_checked :
    tripleExtensionFilterBool smallTripleAnchorA_2 smallTripleAnchorB_2
      smallTripleAnchorC_2 smallTriplePairClosure_2 smallTripleAllowed_2 = true := by sorry



end D1Bound5
end
