-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_002_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_002_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:25:04.867677+00:00
-- url     : https://prove2.me/theorems/2b06f9dc-1413-460e-be24-fa9887d63274
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 1
-- statement:
--   For prepared pair 28, left list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 196 through 207, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_002Part01.lean, lines 10-14, SHA-256 a98a0e22435018f8c9875754dc17c3e399d26fd724ee96adf5213a3efa224be7. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_002_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 196) (PairLightPrepared28.leftRows.drop 196) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
