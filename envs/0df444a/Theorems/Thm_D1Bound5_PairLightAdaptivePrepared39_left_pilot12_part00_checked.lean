-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_pilot12_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.left_pilot12_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:41.718801+00:00
-- url     : https://prove2.me/theorems/4dbd6cf0-3367-4273-b695-6540f05c1612
-- title:
--   Selected-floor prefix certificate for prepared pair 39, left list, part 0
-- statement:
--   For prepared pair 39, left list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 0 through 11, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft39_Pilot12Part00.lean, lines 11-16, SHA-256 a78286c222b19e2a87b187011aea36cc73c46324a655af49bbf178d2b48a8081. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.left_pilot12_part00_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 12
      (PairLightPrepared39.leftCached.drop 0)
      (PairLightPrepared39.leftRows.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
