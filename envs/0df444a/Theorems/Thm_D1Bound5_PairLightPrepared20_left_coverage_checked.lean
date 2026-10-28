-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared20_left_coverage_checked
-- name    : D1Bound5.PairLightPrepared20.left_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:27:25.172681+00:00
-- url     : https://prove2.me/theorems/14dee554-95c1-4841-b582-adfe60712678
-- title:
--   Pair Light Prepared20 — left coverage checked
-- statement:
--   Auxiliary result `PairLightPrepared20.left_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft20.lean, lines 9-11, SHA-256 40d9e01bffe2f380241ad601110de24daff418a25d6d96f5c7ee5087ede69153. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_002

section
namespace D1Bound5.PairLightPrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared20.left_coverage_checked :
    decide (leftCached.map Prod.fst = leftVertices) = true := by sorry







end D1Bound5.PairLightPrepared20
end
