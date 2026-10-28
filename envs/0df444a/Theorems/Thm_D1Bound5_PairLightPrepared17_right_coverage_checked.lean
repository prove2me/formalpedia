-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared17_right_coverage_checked
-- name    : D1Bound5.PairLightPrepared17.right_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:57:14.672394+00:00
-- url     : https://prove2.me/theorems/d8d2dc2c-d9d4-4627-a22e-577195f30ce9
-- title:
--   Pair Light Prepared17 — right coverage checked
-- statement:
--   Auxiliary result `PairLightPrepared17.right_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight17.lean, lines 10-12, SHA-256 5fd224de2ae6bf552ffd1b2f606cf69c4ae290542ebf8a3b431ff524c7dbf213. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_005

section
namespace D1Bound5.PairLightPrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared17.right_coverage_checked :
    decide (rightCached.map Prod.fst = rightVertices) = true := by sorry







end D1Bound5.PairLightPrepared17
end
