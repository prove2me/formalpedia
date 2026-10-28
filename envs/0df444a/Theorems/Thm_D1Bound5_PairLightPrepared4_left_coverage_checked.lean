-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared4_left_coverage_checked
-- name    : D1Bound5.PairLightPrepared4.left_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:25:41.021985+00:00
-- url     : https://prove2.me/theorems/8a390569-3130-4e59-9eec-f642093de629
-- title:
--   Pair Light Prepared4 — left coverage checked
-- statement:
--   Auxiliary result `PairLightPrepared4.left_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft4.lean, lines 13-15, SHA-256 2add7367bc223dc724e8208afedc6ed81c4bf296d5788e6ebeac5334e583c76f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftVertices_Definitions

section
namespace D1Bound5.PairLightPrepared4
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared4.left_coverage_checked :
    decide (leftCached.map Prod.fst = leftVertices) = true := by sorry







end D1Bound5.PairLightPrepared4
end
