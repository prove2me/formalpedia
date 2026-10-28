-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared20_right_coverage_checked
-- name    : D1Bound5.PairLightAdaptivePrepared20.right_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:49:10.95965+00:00
-- url     : https://prove2.me/theorems/95dd0e63-b093-4b56-b03f-eb5affc7189c
-- title:
--   Pair Light Adaptive Prepared20 — right coverage checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared20.right_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation20.lean, lines 16-18, SHA-256 e259ce27ca747b225e8781a98dd62e9401b9ceb60658d9212fbff75221542406. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightAdaptivePrepared20.right_coverage_checked :
    decide (PairLightPrepared20.rightCached.map Prod.fst = PairLightPrepared20.rightVertices) = true := by sorry




end D1Bound5.PairLightAdaptivePrepared20
end
