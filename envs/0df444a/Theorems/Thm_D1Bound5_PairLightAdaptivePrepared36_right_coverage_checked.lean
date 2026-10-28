-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_coverage_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:20:08.628757+00:00
-- url     : https://prove2.me/theorems/8b4f3da6-a2ec-44dc-95a6-65884882174e
-- title:
--   Pair Light Adaptive Prepared36 — right coverage checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared36.right_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation36.lean, lines 16-18, SHA-256 240871f1b54ab24ee38331ca1a4d007af0d72d92a6af2f35022eabf55b7ed9fa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_coverage_checked :
    decide (PairLightPrepared36.rightCached.map Prod.fst = PairLightPrepared36.rightVertices) = true := by sorry




end D1Bound5.PairLightAdaptivePrepared36
end
