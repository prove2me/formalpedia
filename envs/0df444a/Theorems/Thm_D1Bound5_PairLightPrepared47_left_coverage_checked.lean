-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared47_left_coverage_checked
-- name    : D1Bound5.PairLightPrepared47.left_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:34:04.032345+00:00
-- url     : https://prove2.me/theorems/3d9eef0d-1431-4519-8f26-afb9e01a554c
-- title:
--   Pair Light Prepared47 — left coverage checked
-- statement:
--   Auxiliary result `PairLightPrepared47.left_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft47.lean, lines 7-9, SHA-256 3e8d45055b201733f4da8d677cdf32ca10aba4e85a7df53bec0a2f2dbec1274d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData47_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData47_Definitions_002

section
namespace D1Bound5.PairLightPrepared47
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared47.left_coverage_checked :
    decide (leftCached.map Prod.fst = leftVertices) = true := by sorry







end D1Bound5.PairLightPrepared47
end
