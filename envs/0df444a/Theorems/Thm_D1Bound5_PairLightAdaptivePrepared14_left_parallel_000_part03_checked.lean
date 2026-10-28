-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_parallel_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:57.550437+00:00
-- url     : https://prove2.me/theorems/2f37ac7c-3da2-4279-8800-1fa4e0d7f994
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list, part 3
-- statement:
--   For prepared pair 14, left list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 36 through 47, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft14_000Part03.lean, lines 10-14, SHA-256 29b362c298b849e42a7dd2a061aa8d065d6dd64b76895cd4365d791d031c1fc1. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_parallel_000_part03_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 36) (PairLightPrepared14.leftRows.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
