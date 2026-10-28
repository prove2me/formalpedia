-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part14_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part14_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:10.785998+00:00
-- url     : https://prove2.me/theorems/017bd4d9-4a5f-4d62-aced-9296dd3eecc4
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 14
-- statement:
--   For prepared pair 36, left list, part 14, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 454 through 465, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_003Part14.lean, lines 10-14, SHA-256 5a4e7b617f8ed6ca064802e51f9539cbd8527851a5ceb88e3e1317b972319f69. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part14_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 454) (PairLightPrepared36.leftRows.drop 454) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
