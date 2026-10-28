-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared20_right_coverage_checked
-- name    : D1Bound5.PairLightPrepared20.right_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:49:14.485147+00:00
-- url     : https://prove2.me/theorems/872051fd-9702-4d3c-ad0f-34d71b8c467b
-- title:
--   Pair Light Prepared20 — right coverage checked
-- statement:
--   Auxiliary result `PairLightPrepared20.right_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight20.lean, lines 9-11, SHA-256 58b6b5b1ae790cff7408d6ecfe0ed47e733d5d10e8ae38db09441ffcb0a6f1b5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_004

section
namespace D1Bound5.PairLightPrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared20.right_coverage_checked :
    decide (rightCached.map Prod.fst = rightVertices) = true := by sorry







end D1Bound5.PairLightPrepared20
end
