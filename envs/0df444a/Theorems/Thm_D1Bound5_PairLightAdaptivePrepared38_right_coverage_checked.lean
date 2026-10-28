-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_right_coverage_checked
-- name    : D1Bound5.PairLightAdaptivePrepared38.right_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:16:01.146677+00:00
-- url     : https://prove2.me/theorems/c199614a-d662-4d1f-831b-0371b14d829b
-- title:
--   Pair Light Adaptive Prepared38 — right coverage checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared38.right_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation38.lean, lines 16-18, SHA-256 94da647f45fbb870d7742bdf2493240f9482b52ca245696bbf536545c404bb29. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightAdaptivePrepared38.right_coverage_checked :
    decide (PairLightPrepared38.rightCached.map Prod.fst = PairLightPrepared38.rightVertices) = true := by sorry




end D1Bound5.PairLightAdaptivePrepared38
end
