-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_002_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_002_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:41.168718+00:00
-- url     : https://prove2.me/theorems/003ad68c-d59b-4714-9d1f-8d5583d4bb99
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 5
-- statement:
--   For prepared pair 26, right list, part 5, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 128 through 130; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_002Part05.lean, lines 7-11, SHA-256 8c66454b4999c6808751e8b361e9288a5ddda45cb88a5be6b48c6976f6fc6300. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_002_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached002.drop 15) (rightRows002.drop 15) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
