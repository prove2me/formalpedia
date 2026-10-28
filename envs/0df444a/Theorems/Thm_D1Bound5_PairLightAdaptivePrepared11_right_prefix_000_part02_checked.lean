-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_right_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared11.right_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:30:19.66287+00:00
-- url     : https://prove2.me/theorems/aac6f9c3-20c0-4fd8-bda9-1cf34ce16ba2
-- title:
--   Selected-floor prefix certificate for prepared pair 11, right list, part 2
-- statement:
--   For prepared pair 11, right list, part 2, the selected-floor certificate succeeds for at most `22` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared11.sieve`. Original heads 36 through 57, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight11_000Part02.lean, lines 7-11, SHA-256 a8b296a5abab11995398c02cc33e94445399ad0bf18ddbf793cc76405f42d90d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared11.right_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 22
      (rightCached000.drop 36) (rightRows000.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared11
end
