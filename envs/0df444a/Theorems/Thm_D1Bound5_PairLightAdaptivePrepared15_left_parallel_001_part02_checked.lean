-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_parallel_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:12.665533+00:00
-- url     : https://prove2.me/theorems/21745c46-5e12-477a-b5f7-960f87114842
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list, part 2
-- statement:
--   For prepared pair 15, left list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 116 through 127, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft15_001Part02.lean, lines 10-14, SHA-256 d7b8eda53a69babab9ef8f1bc00f3248d075374512f70adb42a557ae1159abcb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_parallel_001_part02_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.leftCached.drop 116) (PairLightPrepared15.leftRows.drop 116) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
