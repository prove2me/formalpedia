-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:43:37.655176+00:00
-- url     : https://prove2.me/theorems/fcb77037-7586-43c3-b85a-c146ed4b6fb3
-- title:
--   Selected-floor prefix certificate for prepared pair 17, left list
-- statement:
--   For prepared pair 17, left list, the selected-floor certificate succeeds for at most `223` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Heads 137 through 359; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft17_001.lean, lines 11-29, SHA-256 4fd8d83e713b51b6703768b856234cf95ff1c8c62f045c87b8a7297faf9a5c08. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 223
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
