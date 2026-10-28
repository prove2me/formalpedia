-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_000_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.right_prefix_000_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:05.418466+00:00
-- url     : https://prove2.me/theorems/95933644-fda1-4c23-b19d-ed68d279fe4d
-- title:
--   Selected-floor prefix certificate for prepared pair 39, right list, part 8
-- statement:
--   For prepared pair 39, right list, part 8, the selected-floor certificate succeeds for at most `2` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 96 through 97, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight39_000Part08.lean, lines 11-16, SHA-256 de01d9b43cd375f952b12663331b1e5080c8c79f8c9eac244c6712fe9e1ce556. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.right_prefix_000_part08_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 2
      (PairLightPrepared39.rightCached.drop 96)
      (PairLightPrepared39.rightRows.drop 96) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
