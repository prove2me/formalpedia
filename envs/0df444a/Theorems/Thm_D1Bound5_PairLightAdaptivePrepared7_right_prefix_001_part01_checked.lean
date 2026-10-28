-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.right_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:29:12.771984+00:00
-- url     : https://prove2.me/theorems/7dbcf029-d8e5-42a3-bbb5-97ed85cd0745
-- title:
--   Selected-floor prefix certificate for prepared pair 7, right list, part 1
-- statement:
--   For prepared pair 7, right list, part 1, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 130 through 153, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight7_001Part01.lean, lines 11-16, SHA-256 36541541e5eeaa4fefdb1de236503934782117fa0080a0a2f23d1a4457bf74ba. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.right_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 24
      (PairLightPrepared7.rightCached.drop 130)
      (PairLightPrepared7.rightRows.drop 130) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
