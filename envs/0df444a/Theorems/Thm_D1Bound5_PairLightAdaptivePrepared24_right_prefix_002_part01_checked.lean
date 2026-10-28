-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_prefix_002_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.right_prefix_002_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:19.183561+00:00
-- url     : https://prove2.me/theorems/df789209-64c2-4099-987c-8a48b23e29d2
-- title:
--   Selected-floor prefix certificate for prepared pair 24, right list, part 1
-- statement:
--   For prepared pair 24, right list, part 1, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 272 through 295, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight24_002Part01.lean, lines 11-16, SHA-256 feb215c777287198c053bf8734681e98c1919189cd607bb4aa2a726ea914a24e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.right_prefix_002_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.rightCached.drop 272)
      (PairLightPrepared24.rightRows.drop 272) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
