-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_002_part17_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part17_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:50.420201+00:00
-- url     : https://prove2.me/theorems/dce1f485-b876-415f-badd-a10e8ebff181
-- title:
--   Selected-floor prefix certificate for prepared pair 30, right list, part 17
-- statement:
--   For prepared pair 30, right list, part 17, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 418 through 429, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight30_002Part17.lean, lines 10-14, SHA-256 2d31e43905915c36ceca5728acebe02db49bc4091438973e05c073ad7fe210ee. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part17_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 418) (PairLightPrepared30.rightRows.drop 418) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
