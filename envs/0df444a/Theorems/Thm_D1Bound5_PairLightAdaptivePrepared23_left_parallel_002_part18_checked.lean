-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part18_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part18_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:55.573578+00:00
-- url     : https://prove2.me/theorems/628699c7-eded-4cc5-afc9-3cd518f7d7c2
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list, part 18
-- statement:
--   For prepared pair 23, left list, part 18, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 428 through 439, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft23_002Part18.lean, lines 10-14, SHA-256 53e71bc0bb5995b7e6757d8c64ea6539a871439b69177622258a68be0e3111e8. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part18_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.leftCached.drop 428) (PairLightPrepared23.leftRows.drop 428) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
