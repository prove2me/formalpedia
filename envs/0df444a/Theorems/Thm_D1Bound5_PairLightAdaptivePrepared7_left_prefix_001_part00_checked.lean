-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.left_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:30.345283+00:00
-- url     : https://prove2.me/theorems/4b1f5226-60d9-4956-b4a2-bc98f67e69e2
-- title:
--   Selected-floor prefix certificate for prepared pair 7, left list, part 0
-- statement:
--   For prepared pair 7, left list, part 0, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 105 through 128, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft7_001Part00.lean, lines 11-16, SHA-256 1d7a9b700f8847aeb3f3dbc1a85713bcce07507876141577bf9726e92b2303d6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.left_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 24
      (PairLightPrepared7.leftCached.drop 105)
      (PairLightPrepared7.leftRows.drop 105) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
