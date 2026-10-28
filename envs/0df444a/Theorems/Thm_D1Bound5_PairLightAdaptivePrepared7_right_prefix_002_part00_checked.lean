-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.right_prefix_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:33.115706+00:00
-- url     : https://prove2.me/theorems/546077c6-c452-4177-85f7-fd12a1d77645
-- title:
--   Selected-floor prefix certificate for prepared pair 7, right list, part 0
-- statement:
--   For prepared pair 7, right list, part 0, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 272 through 295, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight7_002Part00.lean, lines 11-16, SHA-256 577647c1ae45b9c4c0b3d9e6812b8ae7003810bdc911372adb4f12318be85db1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.right_prefix_002_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 24
      (PairLightPrepared7.rightCached.drop 272)
      (PairLightPrepared7.rightRows.drop 272) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
