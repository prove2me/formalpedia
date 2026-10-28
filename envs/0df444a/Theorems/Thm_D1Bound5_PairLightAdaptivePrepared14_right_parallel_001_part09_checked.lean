-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_001_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_001_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:41.655358+00:00
-- url     : https://prove2.me/theorems/9acc83b6-7e5c-419c-b4d7-af9622ab59b5
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 9
-- statement:
--   For prepared pair 14, right list, part 9, the selected-floor certificate succeeds for at most `6` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 196 through 201, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_001Part09.lean, lines 10-14, SHA-256 9c8ef9af24c81320a312f8d6e421ad5c9d5192acf188577bc31964038d08f828. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_001_part09_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 6
      (PairLightPrepared14.rightCached.drop 196) (PairLightPrepared14.rightRows.drop 196) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
