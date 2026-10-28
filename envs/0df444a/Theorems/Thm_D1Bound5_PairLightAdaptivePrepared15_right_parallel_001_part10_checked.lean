-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_001_part10_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_001_part10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:25.501268+00:00
-- url     : https://prove2.me/theorems/059dd692-6d46-4e79-92f9-884dceff4ce4
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 10
-- statement:
--   For prepared pair 15, right list, part 10, the selected-floor certificate succeeds for at most `2` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 212 through 213, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_001Part10.lean, lines 10-14, SHA-256 2818dd785f756dfc2cb82101a2822527714cf48b5f003d7a0838dffa328e8d95. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_001_part10_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 2
      (PairLightPrepared15.rightCached.drop 212) (PairLightPrepared15.rightRows.drop 212) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
