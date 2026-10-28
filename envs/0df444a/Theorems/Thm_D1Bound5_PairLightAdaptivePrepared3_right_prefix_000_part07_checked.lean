-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_000_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.right_prefix_000_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:30:18.614568+00:00
-- url     : https://prove2.me/theorems/73fa5f0d-fa2c-4a18-b385-29bd750b59e5
-- title:
--   Selected-floor prefix certificate for prepared pair 3, right list, part 7
-- statement:
--   For prepared pair 3, right list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 84 through 95, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight3_000Part07.lean, lines 10-15, SHA-256 336dc5c69a91550600e652f6e2403712f7fc3ef7c2d9fc1f0048275fa9d5e7a4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.right_prefix_000_part07_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 12
      (PairLightPrepared3.rightCached.drop 84)
      (PairLightPrepared3.rightRows.drop 84) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
