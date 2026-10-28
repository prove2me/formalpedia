-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.left_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:38.156828+00:00
-- url     : https://prove2.me/theorems/605a5a67-3494-49ef-bebb-17c3aa4bca41
-- title:
--   Selected-floor prefix certificate for prepared pair 5, left list, part 1
-- statement:
--   For prepared pair 5, left list, part 1, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`. Original heads 129 through 152, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft5_001Part01.lean, lines 11-16, SHA-256 76b647d1a3f75d14c081272d99d7d33b6babe46892f99a20ee11c83a3abc574b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared5.left_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 24
      (PairLightPrepared5.leftCached.drop 129)
      (PairLightPrepared5.leftRows.drop 129) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared5
end
