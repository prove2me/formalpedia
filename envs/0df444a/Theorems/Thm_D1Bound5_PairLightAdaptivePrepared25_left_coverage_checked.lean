-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_left_coverage_checked
-- name    : D1Bound5.PairLightAdaptivePrepared25.left_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:07:05.061116+00:00
-- url     : https://prove2.me/theorems/81af85c9-a341-451c-9118-c469c33c373f
-- title:
--   Pair Light Adaptive Prepared25 — left coverage checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared25.left_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation25.lean, lines 7-9, SHA-256 dcd94f331a3c1cf22d2b8173fdb1aadc3ce87eeb575f95634fd55f7933df1e4c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared25.left_coverage_checked :
    decide (PairLightPrepared25.leftCached.map Prod.fst = PairLightPrepared25.leftVertices) = true := by sorry








end D1Bound5.PairLightAdaptivePrepared25
end
