-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_prefix_001_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.right_prefix_001_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:23.333601+00:00
-- url     : https://prove2.me/theorems/ea360720-fc22-42cf-9324-2b1bf49c8e72
-- title:
--   Selected-floor prefix certificate for prepared pair 24, right list, part 6
-- statement:
--   For prepared pair 24, right list, part 6, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 245 through 247, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight24_001Part06.lean, lines 11-16, SHA-256 1af5e6fe652a7b6d609c37497c47e1396dd4b8dcef09fe6f847415dfc16f0acc. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.right_prefix_001_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 3
      (PairLightPrepared24.rightCached.drop 245)
      (PairLightPrepared24.rightRows.drop 245) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
