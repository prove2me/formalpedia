-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_002_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.left_prefix_002_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:18.722648+00:00
-- url     : https://prove2.me/theorems/44c580af-4c97-4c20-944f-8b68c1637935
-- title:
--   Selected-floor prefix certificate for prepared pair 7, left list, part 6
-- statement:
--   For prepared pair 7, left list, part 6, the selected-floor certificate succeeds for at most `20` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 412 through 431, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft7_002Part06.lean, lines 11-16, SHA-256 8c4491c2a686517d0cc36ffcc3c3ec089fe4563069a5f6b1fc37da7efb9f22c6. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.left_prefix_002_part06_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 20
      (PairLightPrepared7.leftCached.drop 412)
      (PairLightPrepared7.leftRows.drop 412) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
