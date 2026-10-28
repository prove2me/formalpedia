-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_002_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_002_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:05.933989+00:00
-- url     : https://prove2.me/theorems/e0444793-c3cb-4a92-a4fe-57cf05f8e937
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list, part 5
-- statement:
--   For prepared pair 10, left list, part 5, the selected-floor certificate succeeds for at most `19` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 236 through 254, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_002Part05.lean, lines 11-16, SHA-256 0773cd8ea75d8c17b85ba0ae817550d784a9ba655fb6f2d6f9ca71461b7e8e0e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_002_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 19
      (PairLightPrepared10.leftCached.drop 236)
      (PairLightPrepared10.leftRows.drop 236) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
