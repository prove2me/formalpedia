-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared18_left_coverage_checked
-- name    : D1Bound5.PairLightPrepared18.left_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:19:54.457617+00:00
-- url     : https://prove2.me/theorems/9b68f47a-c5b5-4bda-9b93-fc026374f820
-- title:
--   Pair Light Prepared18 — left coverage checked
-- statement:
--   Auxiliary result `PairLightPrepared18.left_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft18.lean, lines 9-11, SHA-256 f3b772d85e949b23d37eae2f4ec196a7482370c13defa0d20d79ad50f1868c65. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_002

section
namespace D1Bound5.PairLightPrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared18.left_coverage_checked :
    decide (leftCached.map Prod.fst = leftVertices) = true := by sorry







end D1Bound5.PairLightPrepared18
end
