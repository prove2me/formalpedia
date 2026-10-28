-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared13_left_coverage_checked
-- name    : D1Bound5.PairLightAdaptivePrepared13.left_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:26:55.036675+00:00
-- url     : https://prove2.me/theorems/755129e1-8ecc-45f6-857a-90ce7aa8bb7d
-- title:
--   Pair Light Adaptive Prepared13 — left coverage checked
-- statement:
--   Auxiliary result `PairLightAdaptivePrepared13.left_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAdaptiveValidation13.lean, lines 7-9, SHA-256 db51cbf6dcfa9dda59b6422ecb27bdfb1fcbe9cbe8bccc8ae2f1fe40c5b5fa81. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared13.left_coverage_checked :
    decide (PairLightPrepared13.leftCached.map Prod.fst = PairLightPrepared13.leftVertices) = true := by sorry








end D1Bound5.PairLightAdaptivePrepared13
end
