-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_002_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.left_prefix_002_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:41.344513+00:00
-- url     : https://prove2.me/theorems/740a8182-479b-4851-b009-a43837e6b954
-- title:
--   Selected-floor prefix certificate for prepared pair 7, left list, part 1
-- statement:
--   For prepared pair 7, left list, part 1, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 292 through 315, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft7_002Part01.lean, lines 11-16, SHA-256 f1aa1ee6af0cbbb067f4b3c9f8dc68dfd88f48295ce9f99f24b845ed93231b0f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.left_prefix_002_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 24
      (PairLightPrepared7.leftCached.drop 292)
      (PairLightPrepared7.leftRows.drop 292) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
