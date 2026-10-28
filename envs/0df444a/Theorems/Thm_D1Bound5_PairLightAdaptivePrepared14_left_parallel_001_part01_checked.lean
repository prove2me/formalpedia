-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_parallel_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:04.880128+00:00
-- url     : https://prove2.me/theorems/9b938e87-b8ad-4217-80f0-4bb3b0b55d22
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list, part 1
-- statement:
--   For prepared pair 14, left list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 100 through 111, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft14_001Part01.lean, lines 10-14, SHA-256 6afd369190b1aebf8264e727dd6d81b29d004e9733bc8323a55f5a6401a76d01. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_parallel_001_part01_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 100) (PairLightPrepared14.leftRows.drop 100) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
