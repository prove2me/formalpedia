-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.right_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:05.468987+00:00
-- url     : https://prove2.me/theorems/5baaf6d4-27e0-4a0f-b1b2-03768f6c0ecb
-- title:
--   Selected-floor prefix certificate for prepared pair 19, right list, part 1
-- statement:
--   For prepared pair 19, right list, part 1, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 125 through 148, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight19_001Part01.lean, lines 11-16, SHA-256 5311585fdb7ebb9d54a75384144ddb15a489053fc0d6287ffd810fc3091d68d1. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.right_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.rightCached.drop 125)
      (PairLightPrepared19.rightRows.drop 125) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
