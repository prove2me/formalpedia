-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_parallel_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:01.081996+00:00
-- url     : https://prove2.me/theorems/c50db15e-9fc1-45d7-ba9c-fa7b7086b7d9
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list, part 3
-- statement:
--   For prepared pair 15, left list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 128 through 139, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft15_001Part03.lean, lines 10-14, SHA-256 3cb9746a98258683c105961b7321faf29a98ad9b03204b6ac16839fbb4d6dc0b. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_parallel_001_part03_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.leftCached.drop 128) (PairLightPrepared15.leftRows.drop 128) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
