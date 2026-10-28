-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared46_left_coverage_checked
-- name    : D1Bound5.PairLightPrepared46.left_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:34:53.319759+00:00
-- url     : https://prove2.me/theorems/fc02b873-26a9-46ca-8910-93de88e272fe
-- title:
--   Pair Light Prepared46 — left coverage checked
-- statement:
--   Auxiliary result `PairLightPrepared46.left_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft46.lean, lines 10-12, SHA-256 1f83b52da398d7859b2344f560660efce4764f16abde756d5407b114342d3f4f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_002

section
namespace D1Bound5.PairLightPrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared46.left_coverage_checked :
    decide (leftCached.map Prod.fst = leftVertices) = true := by sorry







end D1Bound5.PairLightPrepared46
end
