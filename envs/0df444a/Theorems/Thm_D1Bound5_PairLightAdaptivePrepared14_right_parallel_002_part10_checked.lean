-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part10_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_002_part10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:13.697291+00:00
-- url     : https://prove2.me/theorems/445b3d99-f412-44ac-935d-2571cd02214f
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 10
-- statement:
--   For prepared pair 14, right list, part 10, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 322 through 333, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_002Part10.lean, lines 10-14, SHA-256 78f621005aafff9640e86ac9176a65b7a4cf2b13269ea0855d914465ad19de91. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_002_part10_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 322) (PairLightPrepared14.rightRows.drop 322) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
