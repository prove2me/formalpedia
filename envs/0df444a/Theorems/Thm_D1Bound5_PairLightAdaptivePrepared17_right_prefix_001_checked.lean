-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_right_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.right_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:45.163976+00:00
-- url     : https://prove2.me/theorems/e75c1bb2-1b73-4762-9af1-f64cd2b252b3
-- title:
--   Selected-floor prefix certificate for prepared pair 17, right list
-- statement:
--   For prepared pair 17, right list, the selected-floor certificate succeeds for at most `220` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Heads 138 through 357; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight17_001.lean, lines 11-29, SHA-256 fef8c95c6c136a9a194fb37d57e50bef60c101429539c5cc9344c9318d329062. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.right_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 220
      rightCached001 rightRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
