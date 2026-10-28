-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared4.left_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:51.180823+00:00
-- url     : https://prove2.me/theorems/10966ab4-aa07-4ded-89e6-812968b7d87f
-- title:
--   Selected-floor prefix certificate for prepared pair 4, left list, part 1
-- statement:
--   For prepared pair 4, left list, part 1, the selected-floor certificate succeeds for at most `11` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared4.sieve`. Original heads 11 through 21, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft4_000Part01.lean, lines 11-16, SHA-256 12444f6fe32ffe79d4f9564205556d4d7892d9f6f49f4c0500c8dc657b23fcac. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared4.left_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 11
      (PairLightPrepared4.leftCached.drop 11)
      (PairLightPrepared4.leftRows.drop 11) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared4
end
