-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_parallel_002_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:22:37.09688+00:00
-- url     : https://prove2.me/theorems/a76eab45-2c1e-4b6b-84a2-3796eed7ca98
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list, part 5
-- statement:
--   For prepared pair 30, left list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 272 through 283, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft30_002Part05.lean, lines 10-14, SHA-256 fc4543809a7b09c6ab208e6d140ff85014bf007f50529831acfc33f19e758e22. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 272) (PairLightPrepared30.leftRows.drop 272) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
