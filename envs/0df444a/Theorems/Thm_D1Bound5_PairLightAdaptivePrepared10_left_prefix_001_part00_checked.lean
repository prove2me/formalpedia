-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared10.left_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:03.420637+00:00
-- url     : https://prove2.me/theorems/a0e30682-67f5-4840-aca1-4a644e6b76cb
-- title:
--   Selected-floor prefix certificate for prepared pair 10, left list, part 0
-- statement:
--   For prepared pair 10, left list, part 0, the selected-floor certificate succeeds for at most `13` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared10.sieve`. Original heads 71 through 83, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft10_001Part00.lean, lines 11-16, SHA-256 662817b57d12d705d0c2a3a8c134cc1fb7f56abc50ee09b60a4c82f4c3e08db7. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared10.left_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 13
      (PairLightPrepared10.leftCached.drop 71)
      (PairLightPrepared10.leftRows.drop 71) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared10
end
