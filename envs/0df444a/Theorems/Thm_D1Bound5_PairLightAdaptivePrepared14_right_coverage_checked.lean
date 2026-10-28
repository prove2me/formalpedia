-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_coverage_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:16:00.596245+00:00
-- url     : https://prove2.me/theorems/63a88881-b5bc-4c2e-b4ca-fed93cc54828
-- title:
--   Pair Light Adaptive Prepared14 — right coverage checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared14.right_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation14.lean, lines 16-18, SHA-256 88acc11635f88ecf148966471161b05f271aff634a15dd0acdb1423630d28286. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_coverage_checked :
    decide (PairLightPrepared14.rightCached.map Prod.fst = PairLightPrepared14.rightVertices) = true := by sorry




end D1Bound5.PairLightAdaptivePrepared14
end
