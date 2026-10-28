-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_002_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.right_prefix_002_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:29:04.011282+00:00
-- url     : https://prove2.me/theorems/78f83419-71ae-41ee-a688-c5448bc27ef1
-- title:
--   Selected-floor prefix certificate for prepared pair 19, right list, part 1
-- statement:
--   For prepared pair 19, right list, part 1, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 272 through 295, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight19_002Part01.lean, lines 11-16, SHA-256 3bff0f0f84ef695cad5cc4dc4fe84b6537e57170060d5ced832b7941ff90b90e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.right_prefix_002_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.rightCached.drop 272)
      (PairLightPrepared19.rightRows.drop 272) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
