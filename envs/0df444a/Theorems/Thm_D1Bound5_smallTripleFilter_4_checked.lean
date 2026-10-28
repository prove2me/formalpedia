-- Prove2me | Theorems.Thm_D1Bound5_smallTripleFilter_4_checked
-- name    : D1Bound5.smallTripleFilter_4_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:39:31.746343+00:00
-- url     : https://prove2.me/theorems/b87cef3c-d925-4ec0-89d6-0d473d88d595
-- title:
--   Small Triple Filter 4 checked
-- statement:
--   Auxiliary result `smallTripleFilter_4_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallTripleExtensionData4.lean, lines 134-137, SHA-256 7b8ce25ff2a1b1bdeba4661beb87f82d9ff11017abd334d7924447d166c581af. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData4_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000













theorem _root_.D1Bound5.smallTripleFilter_4_checked :
    tripleExtensionFilterBool smallTripleAnchorA_4 smallTripleAnchorB_4
      smallTripleAnchorC_4 smallTriplePairClosure_4 smallTripleAllowed_4 = true := by sorry



end D1Bound5
end
