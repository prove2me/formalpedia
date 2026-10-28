-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.left_prefix_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:56.603579+00:00
-- url     : https://prove2.me/theorems/81aba130-90f6-491b-9358-8c99dd359942
-- title:
--   Selected-floor prefix certificate for prepared pair 43, left list, part 0
-- statement:
--   For prepared pair 43, left list, part 0, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 212 through 235, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft43_002Part00.lean, lines 8-13, SHA-256 2caf4cb971b6070806d1f706816a62920b54e2d608543a95c202bed1f394b3ed. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.left_prefix_002_part00_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 24
      (PairLightPrepared43.leftCached.drop 212)
      (PairLightPrepared43.leftRows.drop 212) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
