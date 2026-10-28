-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_001_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.right_prefix_001_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:56:40.663105+00:00
-- url     : https://prove2.me/theorems/eaaa0df8-d9fc-4071-8e10-6ad6f708d787
-- title:
--   Selected-floor prefix certificate for prepared pair 39, right list, part 5
-- statement:
--   For prepared pair 39, right list, part 5, the selected-floor certificate succeeds for at most `18` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 218 through 235, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight39_001Part05.lean, lines 11-16, SHA-256 8d07058fd608e42a2ccb0939c5612cc51c5a42064658dc386b36d51402ac73e5. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.right_prefix_001_part05_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 18
      (PairLightPrepared39.rightCached.drop 218)
      (PairLightPrepared39.rightRows.drop 218) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
