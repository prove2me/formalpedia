-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_left_pilot12_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.left_pilot12_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:06.937948+00:00
-- url     : https://prove2.me/theorems/dc95ee53-228a-4356-b922-56ae4698dde4
-- title:
--   Selected-floor prefix certificate for prepared pair 24, left list, part 0
-- statement:
--   For prepared pair 24, left list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 0 through 11, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft24_Pilot12Part00.lean, lines 11-16, SHA-256 63261baefca4c3abcff4979f5adad44bc6ec7c91ef33259d73062bd777931687. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.left_pilot12_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 12
      (PairLightPrepared24.leftCached.drop 0)
      (PairLightPrepared24.leftRows.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
