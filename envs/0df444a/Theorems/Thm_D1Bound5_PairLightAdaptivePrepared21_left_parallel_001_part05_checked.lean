-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_parallel_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:00.983514+00:00
-- url     : https://prove2.me/theorems/70918d25-11f6-439a-b65a-5d058a74ebaf
-- title:
--   Selected-floor prefix certificate for prepared pair 21, left list, part 5
-- statement:
--   For prepared pair 21, left list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 142 through 153, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft21_001Part05.lean, lines 10-14, SHA-256 3a1f9623a4bc313251428646eab3148811258ce6ab6060f0552c8a96dd6fb328. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_parallel_001_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 142) (PairLightPrepared21.leftRows.drop 142) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
