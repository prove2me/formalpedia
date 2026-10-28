-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_002_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_002_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:54:54.367328+00:00
-- url     : https://prove2.me/theorems/a9413f65-a571-4e52-8123-f0c8202d6d18
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 4
-- statement:
--   For prepared pair 36, left list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 215 through 226, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_002Part04.lean, lines 10-14, SHA-256 db492f6c294127b6f91380b3500ca21e0f80a2c6137fe7fa476f4decb1a795bc. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_002_part04_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 215) (PairLightPrepared36.leftRows.drop 215) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
