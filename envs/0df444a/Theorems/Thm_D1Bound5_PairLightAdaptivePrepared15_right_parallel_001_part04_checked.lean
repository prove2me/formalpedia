-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_001_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_001_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:39.229878+00:00
-- url     : https://prove2.me/theorems/38d0aa9e-2e69-4e84-8c07-e32f4d2f7e62
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 4
-- statement:
--   For prepared pair 15, right list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 140 through 151, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_001Part04.lean, lines 10-14, SHA-256 d88a974c83de3b86b47d55b930985ae3f3609772421f845e9f9efefaf94b9ddc. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_001_part04_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 140) (PairLightPrepared15.rightRows.drop 140) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
