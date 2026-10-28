-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_002_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.right_prefix_002_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:11.288492+00:00
-- url     : https://prove2.me/theorems/c4fc8b64-9bdf-4dae-92ad-4b6a8559f2d2
-- title:
--   Selected-floor prefix certificate for prepared pair 5, right list, part 6
-- statement:
--   For prepared pair 5, right list, part 6, the selected-floor certificate succeeds for at most `14` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`. Original heads 416 through 429, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight5_002Part06.lean, lines 11-16, SHA-256 fe6c6552f4f97468055e96ee347ad0dea78f8e0ced694cb4a32099ea6113d9fa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared5.right_prefix_002_part06_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 14
      (PairLightPrepared5.rightCached.drop 416)
      (PairLightPrepared5.rightRows.drop 416) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared5
end
