-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_001_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_001_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:47.41373+00:00
-- url     : https://prove2.me/theorems/dc65cd4c-b6d8-40bf-8606-9f0cda76a7f8
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 8
-- statement:
--   For prepared pair 30, left list, part 8, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 187 through 198, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_001Part08.lean, lines 10-14, SHA-256 8794388c39f880647f8406514ba967cde560b07a455c4eb59a41f2729bee3a9b. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_001_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 187) (PairLightPrepared30.leftRows.drop 187) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
