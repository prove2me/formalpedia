-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_001_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_001_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:49.226971+00:00
-- url     : https://prove2.me/theorems/24f7eae2-1697-4eed-b4e0-1b5e9bc10347
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 7
-- statement:
--   For prepared pair 14, right list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 172 through 183, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_001Part07.lean, lines 10-14, SHA-256 9156680fcf0e6100f3975b03e51efbda4552b0d5bdf8b596163ce0f375328bb2. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_001_part07_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 172) (PairLightPrepared14.rightRows.drop 172) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
