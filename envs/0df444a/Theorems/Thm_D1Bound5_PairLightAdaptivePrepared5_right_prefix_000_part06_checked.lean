-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_000_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.right_prefix_000_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:39.270273+00:00
-- url     : https://prove2.me/theorems/618c14a2-4ee8-4991-9201-ee6af665079a
-- title:
--   Selected-floor prefix certificate for prepared pair 5, right list, part 6
-- statement:
--   For prepared pair 5, right list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`. Original heads 72 through 83, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight5_000Part06.lean, lines 11-16, SHA-256 4e5416bef865e76131cc63a44b49de3e6562377f8461d41fd8041a9b57899443. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared5.right_prefix_000_part06_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 12
      (PairLightPrepared5.rightCached.drop 72)
      (PairLightPrepared5.rightRows.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared5
end
