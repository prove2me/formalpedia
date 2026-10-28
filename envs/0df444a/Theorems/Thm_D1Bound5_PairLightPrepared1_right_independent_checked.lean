-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared1_right_independent_checked
-- name    : D1Bound5.PairLightPrepared1.right_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:49:13.163853+00:00
-- url     : https://prove2.me/theorems/34e6c951-842b-4a8b-a63f-fc6b337f4859
-- title:
--   Pair Light Prepared1 — right independent checked
-- statement:
--   Auxiliary result `PairLightPrepared1.right_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight1.lean, lines 18-33, SHA-256 14a6e009deda71ce4e221f11d26eed1ef8c5b5705ccb1eae2c7f7cb9343d4a87. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData1RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Right_Definitions_002

section
namespace D1Bound5.PairLightPrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared1.right_independent_checked :
    pairLightSelectedFloorIndependentBool 0 1 sieve rightCached rightRows = true := by sorry



end D1Bound5.PairLightPrepared1
end
