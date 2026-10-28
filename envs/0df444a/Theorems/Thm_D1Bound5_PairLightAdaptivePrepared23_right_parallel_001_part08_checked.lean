-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_parallel_001_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_parallel_001_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:44.822668+00:00
-- url     : https://prove2.me/theorems/3fd3c957-b00b-4f43-b641-3bba2baca71f
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list, part 8
-- statement:
--   For prepared pair 23, right list, part 8, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 188 through 199, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight23_001Part08.lean, lines 10-14, SHA-256 9bd83e55bdc0395c47a0d24129088b6c1b3282d1dc58a0d5a4a05aa16b3e7ba7. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_parallel_001_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.rightCached.drop 188) (PairLightPrepared23.rightRows.drop 188) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
