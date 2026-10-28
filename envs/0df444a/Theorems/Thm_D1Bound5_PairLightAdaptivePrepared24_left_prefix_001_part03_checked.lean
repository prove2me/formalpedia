-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_left_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.left_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:31:20.357007+00:00
-- url     : https://prove2.me/theorems/a88ad7d5-4ff5-4f62-a406-2c7483adf0ef
-- title:
--   Selected-floor prefix certificate for prepared pair 24, left list, part 3
-- statement:
--   For prepared pair 24, left list, part 3, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 173 through 196, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft24_001Part03.lean, lines 11-16, SHA-256 6c8f22e56c0c8b13d0a5da7c8710a38053769d2b9eeeebbcaede68c0e87285bb. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.left_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.leftCached.drop 173)
      (PairLightPrepared24.leftRows.drop 173) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
