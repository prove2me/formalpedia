-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_002_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.right_prefix_002_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:42.038376+00:00
-- url     : https://prove2.me/theorems/4213dc77-cb80-42de-8820-515efceb10e5
-- title:
--   Selected-floor prefix certificate for prepared pair 19, right list, part 3
-- statement:
--   For prepared pair 19, right list, part 3, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 320 through 343, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight19_002Part03.lean, lines 11-16, SHA-256 4df33e3faf39f2f331f1872cf8dc14991ec03ee292626dd65ef302565f3c1f3d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.right_prefix_002_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.rightCached.drop 320)
      (PairLightPrepared19.rightRows.drop 320) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
