-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_right_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared40.right_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:15.17581+00:00
-- url     : https://prove2.me/theorems/cba0c716-613e-4e6a-9c4e-3f17ab40b497
-- title:
--   Selected-floor prefix certificate for prepared pair 40, right list, part 1
-- statement:
--   For prepared pair 40, right list, part 1, the selected-floor certificate succeeds for at most `32` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared40.sieve`. Original heads 29 through 60; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight40_000Part01.lean, lines 7-11, SHA-256 078ce1da4870c7d90686c7a710ffd2b559a0b31f6500d34fbebe6513d66e32de. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared40.right_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 32
      (rightCached000.drop 29) (rightRows000.drop 29) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared40
end
