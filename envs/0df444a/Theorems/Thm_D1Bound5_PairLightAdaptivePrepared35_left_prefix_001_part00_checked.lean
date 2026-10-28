-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared35.left_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:13.314334+00:00
-- url     : https://prove2.me/theorems/530ab93d-4f47-4f78-a265-690b14ec15e2
-- title:
--   Selected-floor prefix certificate for prepared pair 35, left list, part 0
-- statement:
--   For prepared pair 35, left list, part 0, the selected-floor certificate succeeds for at most `46` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared35.sieve`. Original heads 132 through 177; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft35_001Part00.lean, lines 7-11, SHA-256 9bb5be366d784f66ff21f5b6f86187dfb276e12ba315dfa3f84aa0744e765b9e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared35.left_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 46
      (leftCached001.drop 0) (leftRows001.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared35
end
