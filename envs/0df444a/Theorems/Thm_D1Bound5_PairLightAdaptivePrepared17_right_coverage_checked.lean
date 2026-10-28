-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_right_coverage_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.right_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:57:06.984789+00:00
-- url     : https://prove2.me/theorems/420118e8-085d-45ea-8f6e-eb17235d8321
-- title:
--   Pair Light Adaptive Prepared17 — right coverage checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared17.right_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation17.lean, lines 16-18, SHA-256 ecd1a3992455db9a56592cadf6502159efa9728654ce8b6620d8ddf69b32a63f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_005

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightAdaptivePrepared17.right_coverage_checked :
    decide (PairLightPrepared17.rightCached.map Prod.fst = PairLightPrepared17.rightVertices) = true := by sorry




end D1Bound5.PairLightAdaptivePrepared17
end
