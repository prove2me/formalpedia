-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:54.933756+00:00
-- url     : https://prove2.me/theorems/4804e0f4-d3e9-4cab-b644-05dac117158f
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 0
-- statement:
--   For prepared pair 36, right list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 76 through 87, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_001Part00.lean, lines 10-14, SHA-256 9040e593c0dc5654060e3d477bf210cd1995232438e519ad12d6e42a71302dcc. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_001_part00_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 76) (PairLightPrepared36.rightRows.drop 76) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
