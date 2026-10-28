-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_001_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_001_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:28.799629+00:00
-- url     : https://prove2.me/theorems/39ee4bc4-fd28-4f0d-b9ef-0277bac5fe79
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 6
-- statement:
--   For prepared pair 30, left list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 163 through 174, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_001Part06.lean, lines 10-14, SHA-256 31082f7ffd2ace478599f4c594f4fdfa26a78a7de3c7b4fe36638775cd522018. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_001_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 163) (PairLightPrepared30.leftRows.drop 163) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
