-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared35.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:37:13.174555+00:00
-- url     : https://prove2.me/theorems/92e81537-ea9c-44ea-986e-f82725f56c04
-- title:
--   Selected-floor prefix certificate for prepared pair 35, left list
-- statement:
--   For prepared pair 35, left list, the selected-floor certificate succeeds for at most `237` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared35.sieve`. Heads 132 through 368; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft35_001.lean, lines 11-29, SHA-256 f51a0033a0b0fed6af92b99f8315b8dcc4411b7c996966b59b01d1a5724d1af7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared35.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 237
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared35
end
