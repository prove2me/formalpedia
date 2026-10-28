-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_parallel_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:12.548253+00:00
-- url     : https://prove2.me/theorems/8f46a87c-e2ce-4094-a1bc-cf194b7ff057
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list, part 0
-- statement:
--   For prepared pair 14, left list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 0 through 11, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft14_000Part00.lean, lines 10-14, SHA-256 fed300f86445817952a78ba2f9bf96e856250ddb77e6c75d9d6188e9b554dc17. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_parallel_000_part00_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 0) (PairLightPrepared14.leftRows.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
