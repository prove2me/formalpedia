-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_001_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_001_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:45.192036+00:00
-- url     : https://prove2.me/theorems/6d237ef1-7c5d-456f-a8b8-d1929f3b4c0f
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 7
-- statement:
--   For prepared pair 36, right list, part 7, the selected-floor certificate succeeds for at most `7` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 160 through 166, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_001Part07.lean, lines 10-14, SHA-256 3a55122e38b62ace691e9259132499e8f683744ab3569dd83e887fec6c937e88. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_001_part07_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 7
      (PairLightPrepared36.rightCached.drop 160) (PairLightPrepared36.rightRows.drop 160) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
