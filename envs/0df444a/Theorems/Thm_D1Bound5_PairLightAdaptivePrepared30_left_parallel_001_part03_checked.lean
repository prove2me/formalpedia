-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:57.633859+00:00
-- url     : https://prove2.me/theorems/3e5f8a32-c046-4d03-81d9-d7bb06808194
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 3
-- statement:
--   For prepared pair 30, left list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 127 through 138, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_001Part03.lean, lines 10-14, SHA-256 0a759a3b62636596db67ef860b4c5ddf1ee87b8383e7841ca6e0a1f2a6b768f2. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 127) (PairLightPrepared30.leftRows.drop 127) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
