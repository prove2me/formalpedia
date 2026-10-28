-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared47_right_signatures_checked
-- name    : D1Bound5.PairLightPrepared47.right_signatures_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:04:26.118651+00:00
-- url     : https://prove2.me/theorems/42bd2f4a-31a2-4f60-8d96-ed0b1631183b
-- title:
--   Pair Light Prepared47 — right signatures checked
-- statement:
--   Auxiliary result `PairLightPrepared47.right_signatures_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight47.lean, lines 11-13, SHA-256 355ed326016df7561798201e0e3affdfea19475d8fa22c49999126fab337ba69. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData47_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData47_Definitions_004

section
namespace D1Bound5.PairLightPrepared47
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.PairLightPrepared47.right_signatures_checked :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true := by sorry





end D1Bound5.PairLightPrepared47
end
