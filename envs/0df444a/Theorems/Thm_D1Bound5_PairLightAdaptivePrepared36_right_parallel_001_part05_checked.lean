-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:20.669345+00:00
-- url     : https://prove2.me/theorems/80f0151a-1c30-4c6a-ac1a-aecc1c257c81
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 5
-- statement:
--   For prepared pair 36, right list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 136 through 147, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_001Part05.lean, lines 10-14, SHA-256 6e2594dceffe36cddd4e6eeeab56f70cc4560119375a0b6d56d7c9cb92131856. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_001_part05_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 136) (PairLightPrepared36.rightRows.drop 136) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
