-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:34.890922+00:00
-- url     : https://prove2.me/theorems/a8b5126a-e5e2-4566-87a9-f665758055d5
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 5
-- statement:
--   For prepared pair 36, left list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 346 through 357, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_003Part05.lean, lines 10-14, SHA-256 eab57408cb7be1ca87ce62e56f2f6046296b73d3ec6a408b416d5797d6110a9c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part05_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 346) (PairLightPrepared36.leftRows.drop 346) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
