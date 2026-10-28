-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_002_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:02.999992+00:00
-- url     : https://prove2.me/theorems/60b47376-a63a-4c1d-84fd-9edc74565dc5
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 9
-- statement:
--   For prepared pair 30, left list, part 9, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 320 through 331, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_002Part09.lean, lines 10-14, SHA-256 c11f79381903c3986aa455e8a4460935ddf5541be7b613aad64fa517e26d2868. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part09_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 320) (PairLightPrepared30.leftRows.drop 320) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
