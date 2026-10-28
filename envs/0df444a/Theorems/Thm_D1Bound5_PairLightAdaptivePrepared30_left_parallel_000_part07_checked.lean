-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_000_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_000_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:48.704978+00:00
-- url     : https://prove2.me/theorems/0dc28d90-3c04-40d8-9796-d8f6aebe7f4e
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 7
-- statement:
--   For prepared pair 30, left list, part 7, the selected-floor certificate succeeds for at most `7` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 84 through 90, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_000Part07.lean, lines 10-14, SHA-256 f18cbcf94f9d7608966b03355ff8ac7c88bc33313c0e156e4392167eaaf09635. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_000_part07_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 7
      (PairLightPrepared30.leftCached.drop 84) (PairLightPrepared30.leftRows.drop 84) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
