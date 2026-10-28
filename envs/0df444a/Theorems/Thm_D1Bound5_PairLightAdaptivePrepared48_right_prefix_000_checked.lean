-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared48.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:51:11.915259+00:00
-- url     : https://prove2.me/theorems/9cec88d2-95ad-4453-9b0c-38c68b3284e3
-- title:
--   Selected-floor prefix certificate for prepared pair 48, right list
-- statement:
--   For prepared pair 48, right list, the selected-floor certificate succeeds for at most `138` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 8, and the sieve is `PairLightPrepared48.sieve`. Heads 0 through 137; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight48_000.lean, lines 13-43, SHA-256 7995390531691efd46a8af8536671fa0111ed2eb703026437a9de7fc6af1bff0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared48.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 138
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared48
end
