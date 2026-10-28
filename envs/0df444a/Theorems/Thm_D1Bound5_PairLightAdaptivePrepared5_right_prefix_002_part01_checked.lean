-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_002_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.right_prefix_002_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:36.974011+00:00
-- url     : https://prove2.me/theorems/e74b70b0-b1c5-4aec-83f4-5eb220128396
-- title:
--   Selected-floor prefix certificate for prepared pair 5, right list, part 1
-- statement:
--   For prepared pair 5, right list, part 1, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`. Original heads 296 through 319, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight5_002Part01.lean, lines 11-16, SHA-256 8bf1e149f6cef2a3116d09a3b8529a8b442f529ea66da11b568cea69f7384952. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared5.right_prefix_002_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 24
      (PairLightPrepared5.rightCached.drop 296)
      (PairLightPrepared5.rightRows.drop 296) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared5
end
