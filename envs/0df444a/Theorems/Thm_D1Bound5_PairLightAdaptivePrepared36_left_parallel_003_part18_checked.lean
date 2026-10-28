-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part18_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part18_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:39.657997+00:00
-- url     : https://prove2.me/theorems/3ed1a44e-be60-428e-ad4b-0820defebd89
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 18
-- statement:
--   For prepared pair 36, left list, part 18, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 502 through 513, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_003Part18.lean, lines 10-14, SHA-256 9375dfe6dbd6a4f41db4eae09fb2e8da8181269a967208fd50d63807555e8aa2. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part18_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 502) (PairLightPrepared36.leftRows.drop 502) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
