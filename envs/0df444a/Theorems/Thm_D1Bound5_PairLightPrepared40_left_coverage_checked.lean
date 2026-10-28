-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared40_left_coverage_checked
-- name    : D1Bound5.PairLightPrepared40.left_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:41:21.6723+00:00
-- url     : https://prove2.me/theorems/60fd5d19-d43a-4d14-a532-12db82e71e90
-- title:
--   Pair Light Prepared40 — left coverage checked
-- statement:
--   Auxiliary result `PairLightPrepared40.left_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft40.lean, lines 10-12, SHA-256 bfd270701140b8217ffca2c5bf17fa40c60056332b14d22eb7351596f71448e0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_002

section
namespace D1Bound5.PairLightPrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared40.left_coverage_checked :
    decide (leftCached.map Prod.fst = leftVertices) = true := by sorry







end D1Bound5.PairLightPrepared40
end
