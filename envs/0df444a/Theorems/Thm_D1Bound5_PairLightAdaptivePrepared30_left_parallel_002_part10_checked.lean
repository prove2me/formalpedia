-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_002_part10_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:38.434044+00:00
-- url     : https://prove2.me/theorems/90d0f77f-75e3-4214-b784-d01a2531714b
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 10
-- statement:
--   For prepared pair 30, left list, part 10, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 332 through 343, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_002Part10.lean, lines 10-14, SHA-256 37c14d2b5ee09432cec897ed9c62154c9d4727e8468f2b94805cd79a1994c8d0. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part10_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 332) (PairLightPrepared30.leftRows.drop 332) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
