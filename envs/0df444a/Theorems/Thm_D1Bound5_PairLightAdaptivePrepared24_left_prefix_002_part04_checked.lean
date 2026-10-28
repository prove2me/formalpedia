-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_left_prefix_002_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.left_prefix_002_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:04.755805+00:00
-- url     : https://prove2.me/theorems/4fdc3ae2-0314-4e3c-9fbf-4a65eef4ae1d
-- title:
--   Selected-floor prefix certificate for prepared pair 24, left list, part 4
-- statement:
--   For prepared pair 24, left list, part 4, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 344 through 367, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft24_002Part04.lean, lines 11-16, SHA-256 81f5bb8578822f13ab0b6f4150d25034d4ac4a88af23e5eef7c3e14185ed661f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.left_prefix_002_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.leftCached.drop 344)
      (PairLightPrepared24.leftRows.drop 344) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
