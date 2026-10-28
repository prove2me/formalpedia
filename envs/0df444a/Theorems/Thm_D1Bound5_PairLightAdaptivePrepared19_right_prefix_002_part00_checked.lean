-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.right_prefix_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:23.741853+00:00
-- url     : https://prove2.me/theorems/7c7be70d-d34a-4aad-92c8-1549bf06d2b0
-- title:
--   Selected-floor prefix certificate for prepared pair 19, right list, part 0
-- statement:
--   For prepared pair 19, right list, part 0, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 248 through 271, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight19_002Part00.lean, lines 11-16, SHA-256 509de94e6339537357fa5e696cae9f6929c0e2654c074dead930cf5e41b62224. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.right_prefix_002_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.rightCached.drop 248)
      (PairLightPrepared19.rightRows.drop 248) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
