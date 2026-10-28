-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared45_right_coverage_checked
-- name    : D1Bound5.PairLightPrepared45.right_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:04:28.582661+00:00
-- url     : https://prove2.me/theorems/4dd0f798-ee42-4db6-b65b-af24e7541a9c
-- title:
--   Pair Light Prepared45 — right coverage checked
-- statement:
--   Auxiliary result `PairLightPrepared45.right_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight45.lean, lines 11-13, SHA-256 10f97ddce5040ab7d5427e03351960110d5781db164d1b0eebc3d1697270c570. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_004

section
namespace D1Bound5.PairLightPrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared45.right_coverage_checked :
    decide (rightCached.map Prod.fst = rightVertices) = true := by sorry







end D1Bound5.PairLightPrepared45
end
