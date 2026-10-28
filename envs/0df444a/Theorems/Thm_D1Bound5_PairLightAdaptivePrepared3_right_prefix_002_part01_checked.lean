-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_002_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.right_prefix_002_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:01.411421+00:00
-- url     : https://prove2.me/theorems/4b6fec73-aa75-4ef8-9bc4-2dddcd66cf2d
-- title:
--   Selected-floor prefix certificate for prepared pair 3, right list, part 1
-- statement:
--   For prepared pair 3, right list, part 1, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 330 through 353, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight3_002Part01.lean, lines 10-15, SHA-256 417d4acb4267b3f05ab0c85fc49dadca4fe48a85af6533348529b5a999506f2b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.right_prefix_002_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 24
      (PairLightPrepared3.rightCached.drop 330)
      (PairLightPrepared3.rightRows.drop 330) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
