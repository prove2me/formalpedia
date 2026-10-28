-- Prove2me | Theorems.Thm_D1Bound5_smallTripleFilter_10_checked
-- name    : D1Bound5.smallTripleFilter_10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:48:53.627985+00:00
-- url     : https://prove2.me/theorems/6136875a-df52-43f9-94f9-6e2280df4b83
-- title:
--   Small Triple Filter 10 checked
-- statement:
--   Auxiliary result `smallTripleFilter_10_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallTripleExtensionData10.lean, lines 84-87, SHA-256 f02e6c8d015b4e0538aba168e1bf2bb6744d45b1838d92210a569eb6c517214d. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData10_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000













theorem _root_.D1Bound5.smallTripleFilter_10_checked :
    tripleExtensionFilterBool smallTripleAnchorA_10 smallTripleAnchorB_10
      smallTripleAnchorC_10 smallTriplePairClosure_10 smallTripleAllowed_10 = true := by sorry



end D1Bound5
end
