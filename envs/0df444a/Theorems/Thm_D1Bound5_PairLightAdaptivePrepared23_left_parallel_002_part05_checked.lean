-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:08.640504+00:00
-- url     : https://prove2.me/theorems/7e429c45-561d-4f4e-8e3c-81d0d9e02ad4
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list, part 5
-- statement:
--   For prepared pair 23, left list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 272 through 283, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft23_002Part05.lean, lines 10-14, SHA-256 1ec5c14d9ae4b45a5cb4d692b761725fe1ff709f7f8ce48c7c0b229a3ec5aa75. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.leftCached.drop 272) (PairLightPrepared23.leftRows.drop 272) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
