-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_002_part21_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part21_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:22.021646+00:00
-- url     : https://prove2.me/theorems/c05109aa-68e8-46d6-92b4-2eb5b88869d1
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 21
-- statement:
--   For prepared pair 30, left list, part 21, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 464 through 475, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_002Part21.lean, lines 10-14, SHA-256 b086d92510f1fa7779bdc43c3bb9f3e8a412ac7a74473457e6b1268764e62216. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part21_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 464) (PairLightPrepared30.leftRows.drop 464) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
