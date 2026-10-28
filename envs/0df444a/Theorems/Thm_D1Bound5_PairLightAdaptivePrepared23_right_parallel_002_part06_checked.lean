-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_parallel_002_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_parallel_002_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:34.197878+00:00
-- url     : https://prove2.me/theorems/0c116a46-0dce-4846-b1c9-05732d96a07a
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list, part 6
-- statement:
--   For prepared pair 23, right list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 286 through 297, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight23_002Part06.lean, lines 10-14, SHA-256 c56e840fa988452cc602ce1677ec319cc6b66982b4e703df940dddd1b5022b55. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_parallel_002_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.rightCached.drop 286) (PairLightPrepared23.rightRows.drop 286) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
