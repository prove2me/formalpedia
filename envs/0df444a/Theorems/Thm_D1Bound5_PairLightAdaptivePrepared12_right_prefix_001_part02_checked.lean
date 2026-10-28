-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_right_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared12.right_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:12.153086+00:00
-- url     : https://prove2.me/theorems/03559983-6f91-42ea-81d4-145613090f58
-- title:
--   Selected-floor prefix certificate for prepared pair 12, right list, part 2
-- statement:
--   For prepared pair 12, right list, part 2, the selected-floor certificate succeeds for at most `94` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared12.sieve`. Original heads 265 through 358; every head retains its complete original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight12_001Part02.lean, lines 7-11, SHA-256 878426ee53f013c31060b802bbfbef7aff1fd0f7e52f8676ac5e8b289582cc25. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared12.right_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 94
      (rightCached001.drop 127) (rightRows001.drop 127) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared12
end
