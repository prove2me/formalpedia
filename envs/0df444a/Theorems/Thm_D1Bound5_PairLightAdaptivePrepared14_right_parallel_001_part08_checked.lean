-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_001_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_001_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:55.808469+00:00
-- url     : https://prove2.me/theorems/e141aaf2-1203-4d7f-abb2-cbcfc9586c22
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 8
-- statement:
--   For prepared pair 14, right list, part 8, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 184 through 195, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_001Part08.lean, lines 10-14, SHA-256 c8e65a8ffc976c5ce7121f3b99848a68dca29c64449a94db0855578f686d5c9d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_001_part08_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 184) (PairLightPrepared14.rightRows.drop 184) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
