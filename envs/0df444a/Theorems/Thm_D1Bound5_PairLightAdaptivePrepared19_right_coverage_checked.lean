-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_coverage_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.right_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:57:38.744993+00:00
-- url     : https://prove2.me/theorems/84bf110a-4d1d-4c2c-9eb4-1d4d5828336e
-- title:
--   Pair Light Adaptive Prepared19 — right coverage checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared19.right_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation19.lean, lines 16-18, SHA-256 567e7b2d41b99a934b2cc3ba0576cc0240ba864d0337a78a7ab846da182f9816. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightAdaptivePrepared19.right_coverage_checked :
    decide (PairLightPrepared19.rightCached.map Prod.fst = PairLightPrepared19.rightVertices) = true := by sorry




end D1Bound5.PairLightAdaptivePrepared19
end
