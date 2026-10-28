-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_left_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared19.left_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:41.318948+00:00
-- url     : https://prove2.me/theorems/c3e07320-8381-48e2-a95e-68f4a5c8f95e
-- title:
--   Selected-floor prefix certificate for prepared pair 19, left list, part 3
-- statement:
--   For prepared pair 19, left list, part 3, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared19.sieve`. Original heads 173 through 196, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft19_001Part03.lean, lines 11-16, SHA-256 85b1ba5419c6e95d5857b7627ba8a29d5c688e1a0f610249624bb2af5e598ce9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared19.left_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.leftCached.drop 173)
      (PairLightPrepared19.leftRows.drop 173) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared19
end
