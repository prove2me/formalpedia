-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part22_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_parallel_002_part22_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:09.00228+00:00
-- url     : https://prove2.me/theorems/9c93104c-832a-4a01-bbd1-87c6c45d83ec
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list, part 22
-- statement:
--   For prepared pair 15, left list, part 22, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 478 through 480, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft15_002Part22.lean, lines 10-14, SHA-256 4ba0a9c254d4ed41ee8c5a6acb2e2443393eb49cb1c0565062eed78a6ef747ca. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_parallel_002_part22_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 3
      (PairLightPrepared15.leftCached.drop 478) (PairLightPrepared15.leftRows.drop 478) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
