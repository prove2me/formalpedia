-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_parallel_001_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_parallel_001_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:30:04.891379+00:00
-- url     : https://prove2.me/theorems/a296470c-ac4b-40ff-afee-4dd2d1f5c49a
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list, part 4
-- statement:
--   For prepared pair 23, right list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 140 through 151, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight23_001Part04.lean, lines 10-14, SHA-256 d697c669f3ce4c005ed34ecee983113b0406b4936d85f004b16e86ce1e6ff279. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_parallel_001_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.rightCached.drop 140) (PairLightPrepared23.rightRows.drop 140) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
