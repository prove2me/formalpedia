-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_prefix_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.right_prefix_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:01.941805+00:00
-- url     : https://prove2.me/theorems/9b5dbf4b-8860-4436-828a-7fea64809aae
-- title:
--   Selected-floor prefix certificate for prepared pair 24, right list, part 5
-- statement:
--   For prepared pair 24, right list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 60 through 71, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight24_000Part05.lean, lines 11-16, SHA-256 23c31455da12ec45408dfcc97d41b2086f2137f1a14ec21e0b3442dbcd915a7d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.right_prefix_000_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 12
      (PairLightPrepared24.rightCached.drop 60)
      (PairLightPrepared24.rightRows.drop 60) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
