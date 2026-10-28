-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared40.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:49:13.7282+00:00
-- url     : https://prove2.me/theorems/85191a35-bc0a-4c6d-83d1-425022be140b
-- title:
--   Selected-floor prefix certificate for prepared pair 40, left list
-- statement:
--   For prepared pair 40, left list, the selected-floor certificate succeeds for at most `137` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared40.sieve`. Heads 0 through 136; every head retains its entire tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft40_000.lean, lines 13-43, SHA-256 fdbb11226b21b3a783368b1cc54f9d95fe996e258cf7ebe9ec19d46f6f485c3c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared40.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 137
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared40
end
