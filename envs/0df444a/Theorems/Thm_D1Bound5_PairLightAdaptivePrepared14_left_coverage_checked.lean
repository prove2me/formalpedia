-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_coverage_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:36:17.889912+00:00
-- url     : https://prove2.me/theorems/6853dabd-975e-45da-8f17-72512d22e5d9
-- title:
--   Pair Light Adaptive Prepared14 — left coverage checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared14.left_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation14.lean, lines 7-9, SHA-256 88acc11635f88ecf148966471161b05f271aff634a15dd0acdb1423630d28286. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_coverage_checked :
    decide (PairLightPrepared14.leftCached.map Prod.fst = PairLightPrepared14.leftVertices) = true := by sorry








end D1Bound5.PairLightAdaptivePrepared14
end
