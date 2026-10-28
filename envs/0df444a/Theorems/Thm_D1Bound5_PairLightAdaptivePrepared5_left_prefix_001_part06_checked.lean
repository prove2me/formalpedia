-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_001_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.left_prefix_001_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:45.695844+00:00
-- url     : https://prove2.me/theorems/167cccba-93b7-4543-9a17-4afaf7e52742
-- title:
--   Selected-floor prefix certificate for prepared pair 5, left list, part 6
-- statement:
--   For prepared pair 5, left list, part 6, the selected-floor certificate succeeds for at most `20` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`. Original heads 249 through 268, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft5_001Part06.lean, lines 11-16, SHA-256 f7c646c96026ce351e16442cccb72b57bf9b0d0d3fc2058011573569aeb15f4c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared5.left_prefix_001_part06_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 20
      (PairLightPrepared5.leftCached.drop 249)
      (PairLightPrepared5.leftRows.drop 249) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared5
end
