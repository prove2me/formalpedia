-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_000_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.left_prefix_000_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:21.796126+00:00
-- url     : https://prove2.me/theorems/eaf64ce3-7ede-4bc1-8eee-f2c24855a36b
-- title:
--   Selected-floor prefix certificate for prepared pair 5, left list, part 8
-- statement:
--   For prepared pair 5, left list, part 8, the selected-floor certificate succeeds for at most `9` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`. Original heads 96 through 104, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft5_000Part08.lean, lines 11-16, SHA-256 aa3594f42cf16e474789ebd404bb8520c6ba80e16e31889e0eddc9c653b24e5e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared5.left_prefix_000_part08_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 9
      (PairLightPrepared5.leftCached.drop 96)
      (PairLightPrepared5.leftRows.drop 96) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared5
end
