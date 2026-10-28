-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.left_prefix_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:01.183169+00:00
-- url     : https://prove2.me/theorems/1b832f70-15dc-4e24-a6e8-add1678a79a7
-- title:
--   Selected-floor prefix certificate for prepared pair 7, left list, part 5
-- statement:
--   For prepared pair 7, left list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 60 through 71, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft7_000Part05.lean, lines 11-16, SHA-256 479d1a1f49ba7edc6a95e2f0d30918ab9daea11d97f7e55f9acba9caef7c0e66. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.left_prefix_000_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 12
      (PairLightPrepared7.leftCached.drop 60)
      (PairLightPrepared7.leftRows.drop 60) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
