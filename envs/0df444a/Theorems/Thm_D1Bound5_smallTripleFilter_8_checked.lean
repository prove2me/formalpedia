-- Prove2me | Theorems.Thm_D1Bound5_smallTripleFilter_8_checked
-- name    : D1Bound5.smallTripleFilter_8_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:37:14.965214+00:00
-- url     : https://prove2.me/theorems/b2eb678f-804a-4993-9ec8-e9a36ffd6c27
-- title:
--   Small Triple Filter 8 checked
-- statement:
--   Auxiliary result `smallTripleFilter_8_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallTripleExtensionData8.lean, lines 86-89, SHA-256 89ae5eb015cc06ce9d904be1f305c074eb3cd3fb88b017eb23ad5593272ca11e. Project: https://github.com/tomislav-math/d1-bound5-lean

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













theorem _root_.D1Bound5.smallTripleFilter_8_checked :
    tripleExtensionFilterBool smallTripleAnchorA_8 smallTripleAnchorB_8
      smallTripleAnchorC_8 smallTriplePairClosure_8 smallTripleAllowed_8 = true := by sorry



end D1Bound5
end
