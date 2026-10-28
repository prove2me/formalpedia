-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_left_prefix_001_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.left_prefix_001_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:00.373318+00:00
-- url     : https://prove2.me/theorems/57bf1aa6-a8f1-4768-b3c6-43e116af1a3c
-- title:
--   Selected-floor prefix certificate for prepared pair 19, left list, part 6
-- statement:
--   For prepared pair 19, left list, part 6, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 245 through 247, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft19_001Part06.lean, lines 11-16, SHA-256 2b09080bde935cbd031db2ba33ad4b09075196a4aaf4a79e883b8eec83b6a9b8. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.left_prefix_001_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 3
      (PairLightPrepared19.leftCached.drop 245)
      (PairLightPrepared19.leftRows.drop 245) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
