-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_right_coverage_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.right_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:04:27.821161+00:00
-- url     : https://prove2.me/theorems/825eabec-1a82-4bec-959d-d15c219b43ba
-- title:
--   Pair Light Adaptive Prepared46 — right coverage checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared46.right_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation46.lean, lines 16-18, SHA-256 3bd0d7c3be7939a8d9b4574daaac7e8327673aa43ccbd104bb79f0896f6d44a2. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Right_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData46Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightAdaptivePrepared46.right_coverage_checked :
    decide (PairLightPrepared46.rightCached.map Prod.fst = PairLightPrepared46.rightVertices) = true := by sorry




end D1Bound5.PairLightAdaptivePrepared46
end
