-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_002_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.left_prefix_002_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:31.427163+00:00
-- url     : https://prove2.me/theorems/0a1bff06-2f94-49c8-8a99-5fdcce2d34ca
-- title:
--   Selected-floor prefix certificate for prepared pair 3, left list, part 4
-- statement:
--   For prepared pair 3, left list, part 4, the selected-floor certificate succeeds for at most `6` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 407 through 412, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft3_002Part04.lean, lines 9-14, SHA-256 968c4b79b060937a13c4b6a01b4dc95fb86e35b2890b9cdca170e7d61fde27d9. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.left_prefix_002_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 6
      (PairLightPrepared3.leftCached.drop 407)
      (PairLightPrepared3.leftRows.drop 407) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
