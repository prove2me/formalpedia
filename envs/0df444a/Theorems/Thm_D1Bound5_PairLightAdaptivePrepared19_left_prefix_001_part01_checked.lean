-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_left_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.left_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:37.935893+00:00
-- url     : https://prove2.me/theorems/86012e79-a15b-42df-bc5e-f070f5140a38
-- title:
--   Selected-floor prefix certificate for prepared pair 19, left list, part 1
-- statement:
--   For prepared pair 19, left list, part 1, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 125 through 148, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft19_001Part01.lean, lines 11-16, SHA-256 a3ea261982c006eb3481cc752059d33bda2d21b5c4f104e55e62a478b88627cb. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.left_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.leftCached.drop 125)
      (PairLightPrepared19.leftRows.drop 125) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
