-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_000_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.left_prefix_000_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:58.923997+00:00
-- url     : https://prove2.me/theorems/13eb3c6b-6f03-4961-924c-5265d0af708c
-- title:
--   Selected-floor prefix certificate for prepared pair 3, left list, part 7
-- statement:
--   For prepared pair 3, left list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 84 through 95, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft3_000Part07.lean, lines 9-14, SHA-256 884bd854fb8c1d246728214db7963dd4c136954737fe8a1f4a80bf8c1fc6d58f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.left_prefix_000_part07_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 12
      (PairLightPrepared3.leftCached.drop 84)
      (PairLightPrepared3.leftRows.drop 84) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
