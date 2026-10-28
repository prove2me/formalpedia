-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_parallel_001_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_parallel_001_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:37.991995+00:00
-- url     : https://prove2.me/theorems/7dca1ddb-8b76-4630-a7ac-dcd8f54303b5
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list, part 9
-- statement:
--   For prepared pair 23, right list, part 9, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 200 through 211, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight23_001Part09.lean, lines 10-14, SHA-256 18c6e0837a1f38e38a50e39854f9d8c557ed5a5047841800bba1dca56ed4cacc. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_parallel_001_part09_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.rightCached.drop 200) (PairLightPrepared23.rightRows.drop 200) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
