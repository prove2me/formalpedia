-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:56:40.842294+00:00
-- url     : https://prove2.me/theorems/66cf2bdc-c326-497d-8cc4-b1894c7bf0c4
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 2
-- statement:
--   For prepared pair 30, left list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 115 through 126, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_001Part02.lean, lines 10-14, SHA-256 232c4ab1926e901589e3101a118f6a40bfe9bb1b4005ec00ee0aeb5f63107a71. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_001_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 115) (PairLightPrepared30.leftRows.drop 115) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
