-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_left_prefix_002_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.left_prefix_002_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:44.139962+00:00
-- url     : https://prove2.me/theorems/cb149858-215e-4f13-b60c-c0a5a15d3fd5
-- title:
--   Selected-floor prefix certificate for prepared pair 24, left list, part 3
-- statement:
--   For prepared pair 24, left list, part 3, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 320 through 343, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft24_002Part03.lean, lines 11-16, SHA-256 94a0805083f034e1b9fb45f5a5f387d3d7f554c10d57916ba18b2cf5e6e2f643. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.left_prefix_002_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.leftCached.drop 320)
      (PairLightPrepared24.leftRows.drop 320) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
