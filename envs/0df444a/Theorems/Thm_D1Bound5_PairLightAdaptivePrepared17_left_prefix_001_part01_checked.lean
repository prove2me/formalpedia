-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.left_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:57.310989+00:00
-- url     : https://prove2.me/theorems/37801c63-c143-44e3-9940-d893f8cc1ddd
-- title:
--   Selected-floor prefix certificate for prepared pair 17, left list, part 1
-- statement:
--   For prepared pair 17, left list, part 1, the selected-floor certificate succeeds for at most `73` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Original heads 187 through 259; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft17_001Part01.lean, lines 7-11, SHA-256 b796db53c22d8130eb10e8f6dbb7bb2508f4f626f175fcd1186353b502953ddd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.left_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 73
      (leftCached001.drop 50) (leftRows001.drop 50) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
