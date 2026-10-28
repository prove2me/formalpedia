-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_000_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.right_prefix_000_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:21.812611+00:00
-- url     : https://prove2.me/theorems/c73fa9dc-9e67-4ed6-8ced-be6cf362fc31
-- title:
--   Selected-floor prefix certificate for prepared pair 19, right list, part 7
-- statement:
--   For prepared pair 19, right list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 84 through 95, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight19_000Part07.lean, lines 11-16, SHA-256 42c52e77a75f5cc37c5de766267688b76245b3f80895df914fb3924f67c64fbf. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.right_prefix_000_part07_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 12
      (PairLightPrepared19.rightCached.drop 84)
      (PairLightPrepared19.rightRows.drop 84) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
