-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_003_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_parallel_003_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:04.325956+00:00
-- url     : https://prove2.me/theorems/807f9b68-f1d4-40b8-b498-436307f0c281
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list, part 4
-- statement:
--   For prepared pair 14, left list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 467 through 478, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft14_003Part04.lean, lines 10-14, SHA-256 bbdfee9bdabddde97ffd7507d131f5e9cfa318b40d199586a0de47c2d54ab0a0. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_parallel_003_part04_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 467) (PairLightPrepared14.leftRows.drop 467) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
