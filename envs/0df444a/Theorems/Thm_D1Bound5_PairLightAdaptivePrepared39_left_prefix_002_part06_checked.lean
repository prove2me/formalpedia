-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_002_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.left_prefix_002_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:46.496761+00:00
-- url     : https://prove2.me/theorems/2c88e5f5-6fd4-4c49-8291-debfbd4e5901
-- title:
--   Selected-floor prefix certificate for prepared pair 39, left list, part 6
-- statement:
--   For prepared pair 39, left list, part 6, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 377 through 400, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft39_002Part06.lean, lines 11-16, SHA-256 4ccc3d6a818cd1124e5a6fac8f5ec6dc3e19b3333e3100ecff7a7ad8f6b49197. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.left_prefix_002_part06_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.leftCached.drop 377)
      (PairLightPrepared39.leftRows.drop 377) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
