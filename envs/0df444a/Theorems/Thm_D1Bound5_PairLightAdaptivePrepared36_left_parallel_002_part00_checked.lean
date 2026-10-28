-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:54.120988+00:00
-- url     : https://prove2.me/theorems/44a04d96-5731-4aa5-b4cc-baf02fa9c557
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 0
-- statement:
--   For prepared pair 36, left list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 167 through 178, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_002Part00.lean, lines 10-14, SHA-256 fbe6daf06d37708ba15e794b0677b0a6776fc33d2e52c77e4a00d2e10872af49. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_002_part00_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 167) (PairLightPrepared36.leftRows.drop 167) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
