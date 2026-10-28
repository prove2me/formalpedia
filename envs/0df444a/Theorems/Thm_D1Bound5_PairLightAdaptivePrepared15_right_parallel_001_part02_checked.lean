-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:30:07.480995+00:00
-- url     : https://prove2.me/theorems/dde2cbd9-6ed1-48c5-b129-fe46d164f54e
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 2
-- statement:
--   For prepared pair 15, right list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 116 through 127, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_001Part02.lean, lines 10-14, SHA-256 b117b5c9662ec68bead1ba944aa68d2182dacee86bcbeda7880aa39bad81749a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_001_part02_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 116) (PairLightPrepared15.rightRows.drop 116) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
