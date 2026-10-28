-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_001_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_parallel_001_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:53.920834+00:00
-- url     : https://prove2.me/theorems/29e1b481-4225-42d5-a20a-a0a80f7a379d
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list, part 4
-- statement:
--   For prepared pair 14, left list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 136 through 147, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft14_001Part04.lean, lines 10-14, SHA-256 9ef1d4566097f83b2e434e85fa1eb1a774521fd9a2af3579abfba08210e4b94b. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_parallel_001_part04_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 136) (PairLightPrepared14.leftRows.drop 136) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
