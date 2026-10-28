-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_002_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.left_prefix_002_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:59.126387+00:00
-- url     : https://prove2.me/theorems/5b1ae64d-a43c-42bd-b517-ceb8f346618f
-- title:
--   Selected-floor prefix certificate for prepared pair 5, left list, part 3
-- statement:
--   For prepared pair 5, left list, part 3, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`. Original heads 341 through 364, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft5_002Part03.lean, lines 11-16, SHA-256 24f55f1d9cc5a1eb91e6f5f846704cade9220055374f5ec8500d27f467e9f47c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared5.left_prefix_002_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 24
      (PairLightPrepared5.leftCached.drop 341)
      (PairLightPrepared5.leftRows.drop 341) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared5
end
