-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared23_left_coverage_checked
-- name    : D1Bound5.PairLightPrepared23.left_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:31:04.073328+00:00
-- url     : https://prove2.me/theorems/192f6356-1220-4d0a-87f5-91e0125a69f8
-- title:
--   Pair Light Prepared23 — left coverage checked
-- statement:
--   Auxiliary result `PairLightPrepared23.left_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft23.lean, lines 11-13, SHA-256 a8f7f099c5ebeef881fb5ac2aeafa4f8ebb79a5760b11c52802ac07a2a60a1aa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftVertices_Definitions

section
namespace D1Bound5.PairLightPrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared23.left_coverage_checked :
    decide (leftCached.map Prod.fst = leftVertices) = true := by sorry







end D1Bound5.PairLightPrepared23
end
