-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:25.868485+00:00
-- url     : https://prove2.me/theorems/5d47a833-e188-41e3-b493-02f20a979b8b
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 0
-- statement:
--   For prepared pair 14, right list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 88 through 99, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_001Part00.lean, lines 10-14, SHA-256 012e83c252b257ee289c97303e4cd678b6cbade62694603658523621a8f2dd8a. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_001_part00_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 88) (PairLightPrepared14.rightRows.drop 88) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
