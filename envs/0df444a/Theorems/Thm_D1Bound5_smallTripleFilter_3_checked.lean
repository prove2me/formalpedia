-- Prove2me | Theorems.Thm_D1Bound5_smallTripleFilter_3_checked
-- name    : D1Bound5.smallTripleFilter_3_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:42:42.58364+00:00
-- url     : https://prove2.me/theorems/78d5dc12-f577-4c5f-94ea-101ca6aaebc6
-- title:
--   Small Triple Filter 3 checked
-- statement:
--   Auxiliary result `smallTripleFilter_3_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallTripleExtensionData3.lean, lines 93-96, SHA-256 463aa620f4230286ba39ef9121676a9c8cc6f5689028ff71b68a2aa01a6062f0. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData3_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000













theorem _root_.D1Bound5.smallTripleFilter_3_checked :
    tripleExtensionFilterBool smallTripleAnchorA_3 smallTripleAnchorB_3
      smallTripleAnchorC_3 smallTriplePairClosure_3 smallTripleAllowed_3 = true := by sorry



end D1Bound5
end
