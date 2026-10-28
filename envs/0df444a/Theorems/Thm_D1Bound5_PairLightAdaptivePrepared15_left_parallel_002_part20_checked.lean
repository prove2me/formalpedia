-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part20_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_parallel_002_part20_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:08.420078+00:00
-- url     : https://prove2.me/theorems/7e38cf24-7e1c-4480-9ac2-2590957d6848
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list, part 20
-- statement:
--   For prepared pair 15, left list, part 20, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 454 through 465, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft15_002Part20.lean, lines 10-14, SHA-256 efc4b603fc88febdc99117df7db2f0b8ec36f0a0b6119dbd9717d45cbf845e6f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_parallel_002_part20_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.leftCached.drop 454) (PairLightPrepared15.leftRows.drop 454) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
