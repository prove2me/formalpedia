-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.left_prefix_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:17.125353+00:00
-- url     : https://prove2.me/theorems/cf0505e6-7b2e-432c-8fb6-58981550a093
-- title:
--   Selected-floor prefix certificate for prepared pair 39, left list, part 5
-- statement:
--   For prepared pair 39, left list, part 5, the selected-floor certificate succeeds for at most `16` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 217 through 232, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft39_001Part05.lean, lines 11-16, SHA-256 e5bdaafc99933b8502358d780f0bcaa9e67ed5d56d7887921030fa0ed75bb16b. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.left_prefix_001_part05_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 16
      (PairLightPrepared39.leftCached.drop 217)
      (PairLightPrepared39.leftRows.drop 217) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
