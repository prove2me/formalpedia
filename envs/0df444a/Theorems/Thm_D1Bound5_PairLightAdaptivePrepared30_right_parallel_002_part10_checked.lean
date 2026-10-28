-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_002_part10_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:12.192993+00:00
-- url     : https://prove2.me/theorems/411318c7-d84e-4310-9b7a-1fb87f0d0a2d
-- title:
--   Selected-floor prefix certificate for prepared pair 30, right list, part 10
-- statement:
--   For prepared pair 30, right list, part 10, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 334 through 345, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight30_002Part10.lean, lines 10-14, SHA-256 3df1295fd06855846f3860bc0b9f03873a6917d73677b294b99553d97f202811. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part10_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 334) (PairLightPrepared30.rightRows.drop 334) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
