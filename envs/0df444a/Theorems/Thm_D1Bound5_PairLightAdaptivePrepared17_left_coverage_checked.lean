-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_coverage_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.left_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:23:36.928392+00:00
-- url     : https://prove2.me/theorems/b302e225-3825-440e-ae82-fd2f77e43da7
-- title:
--   Pair Light Adaptive Prepared17 — left coverage checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared17.left_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation17.lean, lines 7-9, SHA-256 ecd1a3992455db9a56592cadf6502159efa9728654ce8b6620d8ddf69b32a63f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared17.left_coverage_checked :
    decide (PairLightPrepared17.leftCached.map Prod.fst = PairLightPrepared17.leftVertices) = true := by sorry








end D1Bound5.PairLightAdaptivePrepared17
end
