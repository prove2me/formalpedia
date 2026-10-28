-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:22.903468+00:00
-- url     : https://prove2.me/theorems/cba43869-14ff-44bc-9a22-56afa54a2e56
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list, part 6
-- statement:
--   For prepared pair 23, left list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 284 through 295, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft23_002Part06.lean, lines 10-14, SHA-256 86638aa4b606ba980cc34a03842a9c38cb9118dbe69832bef8d5e21ed79482bd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.leftCached.drop 284) (PairLightPrepared23.leftRows.drop 284) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
