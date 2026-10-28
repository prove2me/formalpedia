-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.left_prefix_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:43.311715+00:00
-- url     : https://prove2.me/theorems/829cd9f4-9d99-4f94-a92a-d10a2de76fd4
-- title:
--   Selected-floor prefix certificate for prepared pair 39, left list, part 0
-- statement:
--   For prepared pair 39, left list, part 0, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 233 through 256, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft39_002Part00.lean, lines 11-16, SHA-256 59cec7662826eea6223ba92cde51863595c376151c8dd2bba524a2e18070c9af. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.left_prefix_002_part00_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.leftCached.drop 233)
      (PairLightPrepared39.leftRows.drop 233) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
