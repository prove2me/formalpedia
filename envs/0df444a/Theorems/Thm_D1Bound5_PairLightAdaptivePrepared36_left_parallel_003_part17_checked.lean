-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part17_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part17_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:48.00835+00:00
-- url     : https://prove2.me/theorems/8bed9113-499d-4cac-b776-4b70f79a4804
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 17
-- statement:
--   For prepared pair 36, left list, part 17, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 490 through 501, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_003Part17.lean, lines 10-14, SHA-256 b1057a4383af0bb78313a9f55b14f98f949067e7fff76da5240570c3363dc88d. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part17_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 490) (PairLightPrepared36.leftRows.drop 490) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
