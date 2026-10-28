-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_001_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_001_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:01.41725+00:00
-- url     : https://prove2.me/theorems/3f861838-fa9d-4f9c-9c2d-23b78fa60b61
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 4
-- statement:
--   For prepared pair 36, right list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 124 through 135, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_001Part04.lean, lines 10-14, SHA-256 997e90bce8498c8368f03dfbd5bf305c9d38bde50586edc26d6a3def42bee195. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_001_part04_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 124) (PairLightPrepared36.rightRows.drop 124) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
