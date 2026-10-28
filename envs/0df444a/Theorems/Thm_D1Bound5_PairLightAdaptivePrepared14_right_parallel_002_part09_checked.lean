-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_002_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:57:52.837647+00:00
-- url     : https://prove2.me/theorems/bd319f89-ed92-4713-b839-07c86d98a750
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 9
-- statement:
--   For prepared pair 14, right list, part 9, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 310 through 321, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_002Part09.lean, lines 10-14, SHA-256 bc78dffb9298bc73f1ada9cc94dc7e66cb6cd52b585c829e02ed3e260db6c782. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_002_part09_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 310) (PairLightPrepared14.rightRows.drop 310) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
