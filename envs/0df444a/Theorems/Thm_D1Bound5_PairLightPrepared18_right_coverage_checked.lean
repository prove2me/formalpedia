-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared18_right_coverage_checked
-- name    : D1Bound5.PairLightPrepared18.right_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:10:14.975716+00:00
-- url     : https://prove2.me/theorems/3cf4cf1e-96ef-4d0f-999e-abf9d637bc63
-- title:
--   Pair Light Prepared18 — right coverage checked
-- statement:
--   Auxiliary result `PairLightPrepared18.right_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight18.lean, lines 9-11, SHA-256 a843319ee5d4e3bc2ef6fd5706b9b7e6e3289838b5735a759ddb3cbd14a5aa85. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_004

section
namespace D1Bound5.PairLightPrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared18.right_coverage_checked :
    decide (rightCached.map Prod.fst = rightVertices) = true := by sorry







end D1Bound5.PairLightPrepared18
end
