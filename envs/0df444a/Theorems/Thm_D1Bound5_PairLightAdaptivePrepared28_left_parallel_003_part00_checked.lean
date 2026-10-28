-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_003_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_003_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:48.987033+00:00
-- url     : https://prove2.me/theorems/c18522c0-56b8-4952-b6a6-d109815524cb
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 0
-- statement:
--   For prepared pair 28, left list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 335 through 346, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_003Part00.lean, lines 10-14, SHA-256 09711bccf8c9cdd9e3a03032d1db901c4546c6493847ba4ec4120fa90cf5a2b3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_003_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 335) (PairLightPrepared28.leftRows.drop 335) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
