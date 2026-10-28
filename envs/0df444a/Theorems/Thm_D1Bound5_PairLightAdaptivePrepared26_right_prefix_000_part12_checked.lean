-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_000_part12_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_000_part12_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:49.714905+00:00
-- url     : https://prove2.me/theorems/f368ae57-a3b3-48b7-96ee-8f39c6de56c7
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 12
-- statement:
--   For prepared pair 26, right list, part 12, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Heads 36 through 38 of the original first block; every full tail is retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_000Part12.lean, lines 7-11, SHA-256 adbd0cb0edf90cdd799eda3eb3e578b0a499ca479c41b505c4a34e029d3e5c97. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_000_part12_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached000.drop 36) (rightRows000.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
