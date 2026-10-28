-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_left_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared11.left_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:53:16.15699+00:00
-- url     : https://prove2.me/theorems/dbd89ac5-d321-436d-8c89-801a08893ddd
-- title:
--   Selected-floor prefix certificate for prepared pair 11, left list, part 1
-- statement:
--   For prepared pair 11, left list, part 1, the selected-floor certificate succeeds for at most `20` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared11.sieve`. Original heads 16 through 35, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft11_000Part01.lean, lines 7-11, SHA-256 dd39b7d0db605d76b28faab6156e2e9064ad7098c6f09a4c30d2fa1b677b7308. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared11.left_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 20
      (leftCached000.drop 16) (leftRows000.drop 16) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared11
end
