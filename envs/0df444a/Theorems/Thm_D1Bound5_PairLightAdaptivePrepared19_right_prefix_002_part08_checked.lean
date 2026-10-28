-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_002_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.right_prefix_002_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:53:10.130307+00:00
-- url     : https://prove2.me/theorems/0c770196-a06c-4288-9807-d2cd290852d7
-- title:
--   Selected-floor prefix certificate for prepared pair 19, right list, part 8
-- statement:
--   For prepared pair 19, right list, part 8, the selected-floor certificate succeeds for at most `6` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 440 through 445, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight19_002Part08.lean, lines 11-16, SHA-256 48b87e7e7dd93c99cf53856bc1848cc2b07a197a7b0ca753ca4dfebc3f5affeb. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.right_prefix_002_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 6
      (PairLightPrepared19.rightCached.drop 440)
      (PairLightPrepared19.rightRows.drop 440) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
