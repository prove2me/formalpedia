-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.left_parallel_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:43.18853+00:00
-- url     : https://prove2.me/theorems/3d6f0714-205b-46ca-982b-3e8a6fac7e7b
-- title:
--   Selected-floor prefix certificate for prepared pair 14, left list, part 0
-- statement:
--   For prepared pair 14, left list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 202 through 213, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft14_002Part00.lean, lines 10-14, SHA-256 72b4da990973c7fbde70aec50c5654622b54e615ec53f52ebc77867f98b2042e. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.left_parallel_002_part00_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 202) (PairLightPrepared14.leftRows.drop 202) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
