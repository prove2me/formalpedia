-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_002_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.left_prefix_002_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:39.768188+00:00
-- url     : https://prove2.me/theorems/a7e74f26-3d80-4269-be07-a957d0faa4c9
-- title:
--   Selected-floor prefix certificate for prepared pair 39, left list, part 7
-- statement:
--   For prepared pair 39, left list, part 7, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 401 through 424, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft39_002Part07.lean, lines 11-16, SHA-256 e13a2b326d61560cb60b72754e885aa903e8aa2f31d58a4e38b06d0ef5b45974. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.left_prefix_002_part07_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.leftCached.drop 401)
      (PairLightPrepared39.leftRows.drop 401) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
