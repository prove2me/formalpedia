-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_000_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.left_prefix_000_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:57.368255+00:00
-- url     : https://prove2.me/theorems/65b0997a-6c70-40b7-b320-f09a9a992bc3
-- title:
--   Selected-floor prefix certificate for prepared pair 3, left list, part 6
-- statement:
--   For prepared pair 3, left list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 72 through 83, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft3_000Part06.lean, lines 9-14, SHA-256 ddff9ec3d69de59388ae271b5a4a26c4d945c9ccb1809834d7d021471a2268f5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.left_prefix_000_part06_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 12
      (PairLightPrepared3.leftCached.drop 72)
      (PairLightPrepared3.leftRows.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
