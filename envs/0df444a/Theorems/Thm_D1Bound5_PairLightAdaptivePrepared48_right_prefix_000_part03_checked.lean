-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_right_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared48.right_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:21.720755+00:00
-- url     : https://prove2.me/theorems/a11fa00f-bcdc-477a-a7a2-2376559e3ec6
-- title:
--   Selected-floor prefix certificate for prepared pair 48, right list, part 3
-- statement:
--   For prepared pair 48, right list, part 3, the selected-floor certificate succeeds for at most `41` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 8, and the sieve is `PairLightPrepared48.sieve`. Original heads 96 through 136; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight48_000Part03.lean, lines 7-11, SHA-256 4b61b99568e7e29da63a9526125c0c1829cadf39d0b0ec3e6127446079ada4b8. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared48.right_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 41
      (rightCached000.drop 96) (rightRows000.drop 96) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared48
end
