-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_001_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_001_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:26.686488+00:00
-- url     : https://prove2.me/theorems/e61298ac-85c9-42f0-9462-bb401ac21d57
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 9
-- statement:
--   For prepared pair 15, right list, part 9, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 200 through 211, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_001Part09.lean, lines 10-14, SHA-256 d3b537d35043dc07d899412f821dc7cbe470c9d4468af65be4ef8f502ea9151f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_001_part09_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 200) (PairLightPrepared15.rightRows.drop 200) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
