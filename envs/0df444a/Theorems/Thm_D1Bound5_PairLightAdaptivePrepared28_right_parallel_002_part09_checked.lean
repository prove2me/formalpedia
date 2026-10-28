-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_002_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_002_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:22:41.036361+00:00
-- url     : https://prove2.me/theorems/de4e609d-951a-4de4-8329-9e7c94234841
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 9
-- statement:
--   For prepared pair 28, right list, part 9, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 292 through 303, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_002Part09.lean, lines 10-14, SHA-256 3558680a7240bd9f5e4125c976da44ae14431a3bcdcd8a65a771cd3d344602c7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_002_part09_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 292) (PairLightPrepared28.rightRows.drop 292) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
