-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part21_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part21_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:29:03.272322+00:00
-- url     : https://prove2.me/theorems/e5a1a614-b045-47b6-9fc4-393e83ff8c48
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 21
-- statement:
--   For prepared pair 15, right list, part 21, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 466 through 477, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_002Part21.lean, lines 10-14, SHA-256 6450f3a23192edd3aba7060cf563756689c5ab8e5bf99bb8eb2345dae57e58c7. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part21_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 466) (PairLightPrepared15.rightRows.drop 466) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
