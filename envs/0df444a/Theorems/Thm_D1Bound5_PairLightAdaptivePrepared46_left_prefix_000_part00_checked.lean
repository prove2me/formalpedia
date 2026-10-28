-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_left_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.left_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:37.865001+00:00
-- url     : https://prove2.me/theorems/1c699dc4-180e-4158-9c6d-444f43403a80
-- title:
--   Selected-floor prefix certificate for prepared pair 46, left list, part 0
-- statement:
--   For prepared pair 46, left list, part 0, the selected-floor certificate succeeds for at most `16` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Original heads 0 through 15, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft46_000Part00.lean, lines 7-11, SHA-256 66ce7a36ac8f973813419cf810f374fe6775edaab370f382abd4a7a52984714c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.left_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 16
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
