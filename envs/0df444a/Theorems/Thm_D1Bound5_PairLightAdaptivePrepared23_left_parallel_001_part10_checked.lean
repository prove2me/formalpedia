-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_001_part10_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_parallel_001_part10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:55.568952+00:00
-- url     : https://prove2.me/theorems/d5f40952-bad3-45ad-8ea0-8c5fcbd64f7b
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list, part 10
-- statement:
--   For prepared pair 23, left list, part 10, the selected-floor certificate succeeds for at most `1` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 211 through 211, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft23_001Part10.lean, lines 10-14, SHA-256 fd0d7f4a10b60140c429e208d2eb8259ca9bc2016b0f49b870b827be4aabac21. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_parallel_001_part10_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 1
      (PairLightPrepared23.leftCached.drop 211) (PairLightPrepared23.leftRows.drop 211) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
