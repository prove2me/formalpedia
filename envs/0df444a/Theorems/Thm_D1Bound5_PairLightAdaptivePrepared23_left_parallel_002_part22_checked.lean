-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part22_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part22_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:05.835774+00:00
-- url     : https://prove2.me/theorems/a07c2196-b266-4dde-81ee-e17d0fbc3fd3
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list, part 22
-- statement:
--   For prepared pair 23, left list, part 22, the selected-floor certificate succeeds for at most `6` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 476 through 481, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft23_002Part22.lean, lines 10-14, SHA-256 36a1e40d6342b0f776894e9baa7e7f41fd4cf47e554bd3d2477f1c8b0883a1a0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part22_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 6
      (PairLightPrepared23.leftCached.drop 476) (PairLightPrepared23.leftRows.drop 476) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
