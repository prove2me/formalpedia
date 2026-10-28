-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part14_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part14_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:49.711154+00:00
-- url     : https://prove2.me/theorems/f4977c50-0b67-4962-83b9-32e96fe9f722
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list, part 14
-- statement:
--   For prepared pair 23, left list, part 14, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 380 through 391, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft23_002Part14.lean, lines 10-14, SHA-256 2f07ba1822929fb9ed0480135803b6ce71f1e9d4f2ff071de3fbaaf6c8d605d3. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part14_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.leftCached.drop 380) (PairLightPrepared23.leftRows.drop 380) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
