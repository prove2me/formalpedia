-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part19_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part19_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:46.716989+00:00
-- url     : https://prove2.me/theorems/4987b451-a737-4c0a-a6ff-50cb5a1f7ed4
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 19
-- statement:
--   For prepared pair 15, right list, part 19, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 442 through 453, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_002Part19.lean, lines 10-14, SHA-256 a5cc7fffed5510a7fcfe3a0de2e8fda86b110c0da4169c24cd2dee11e68db55e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part19_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 442) (PairLightPrepared15.rightRows.drop 442) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
