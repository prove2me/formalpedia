-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_coverage_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:24:38.251478+00:00
-- url     : https://prove2.me/theorems/3d90718a-6ad4-48ad-82fd-f5152222e607
-- title:
--   Pair Light Adaptive Prepared36 — left coverage checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared36.left_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation36.lean, lines 7-9, SHA-256 240871f1b54ab24ee38331ca1a4d007af0d72d92a6af2f35022eabf55b7ed9fa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_coverage_checked :
    decide (PairLightPrepared36.leftCached.map Prod.fst = PairLightPrepared36.leftVertices) = true := by sorry








end D1Bound5.PairLightAdaptivePrepared36
end
