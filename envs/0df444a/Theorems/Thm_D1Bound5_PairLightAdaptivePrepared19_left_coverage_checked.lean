-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_left_coverage_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.left_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:36:58.116706+00:00
-- url     : https://prove2.me/theorems/708a9a58-f039-40f8-916d-475e4c380df5
-- title:
--   Pair Light Adaptive Prepared19 — left coverage checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared19.left_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation19.lean, lines 7-9, SHA-256 567e7b2d41b99a934b2cc3ba0576cc0240ba864d0337a78a7ab846da182f9816. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared19.left_coverage_checked :
    decide (PairLightPrepared19.leftCached.map Prod.fst = PairLightPrepared19.leftVertices) = true := by sorry








end D1Bound5.PairLightAdaptivePrepared19
end
