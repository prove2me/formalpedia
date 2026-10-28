-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.left_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:08.62776+00:00
-- url     : https://prove2.me/theorems/910c4641-48e5-40be-b4b5-4a3d4252acce
-- title:
--   Selected-floor prefix certificate for prepared pair 39, left list, part 0
-- statement:
--   For prepared pair 39, left list, part 0, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 97 through 120, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft39_001Part00.lean, lines 11-16, SHA-256 87c0815611bdb9c01ac5ce0e43d03522ad30e2482c753a2633c233468feb6eb6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.left_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.leftCached.drop 97)
      (PairLightPrepared39.leftRows.drop 97) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
