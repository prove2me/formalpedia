-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_coverage_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:32:20.520857+00:00
-- url     : https://prove2.me/theorems/e6616f6d-f164-4fc3-9ad1-0e15cd548739
-- title:
--   Pair Light Adaptive Prepared6 — right coverage checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared6.right_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation6.lean, lines 16-18, SHA-256 28ec548a27c1621ae0a615dd43968304121b99bbb142ea55bc0b3cf0666d651c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_coverage_checked :
    decide (PairLightPrepared6.rightCached.map Prod.fst = PairLightPrepared6.rightVertices) = true := by sorry




end D1Bound5.PairLightAdaptivePrepared6
end
