-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared30_right_coverage_checked
-- name    : D1Bound5.PairLightPrepared30.right_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:13:36.20322+00:00
-- url     : https://prove2.me/theorems/c6351b9e-5c0b-440c-91c2-cb59240888a4
-- title:
--   Pair Light Prepared30 — right coverage checked
-- statement:
--   Auxiliary result `PairLightPrepared30.right_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight30.lean, lines 11-13, SHA-256 83409733b0d34678b133aeb4d1f8937ec990699a0f041073c7bacd00cfff13da. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightVertices_Definitions

section
namespace D1Bound5.PairLightPrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared30.right_coverage_checked :
    decide (rightCached.map Prod.fst = rightVertices) = true := by sorry







end D1Bound5.PairLightPrepared30
end
