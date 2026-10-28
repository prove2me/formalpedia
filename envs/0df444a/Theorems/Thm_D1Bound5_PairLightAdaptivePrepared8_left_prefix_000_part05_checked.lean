-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:57.001481+00:00
-- url     : https://prove2.me/theorems/9025f03f-6ca2-4e4a-a968-1bd265744134
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 5
-- statement:
--   For prepared pair 8, left list, part 5, the selected-floor certificate succeeds for at most `10` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 48 through 57, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_000Part05.lean, lines 11-16, SHA-256 d58495f81a98f06a19a6a36e71a123a3d015dbfc65668985343da032ef524e60. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_000_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 10
      (PairLightPrepared8.leftCached.drop 48)
      (PairLightPrepared8.leftRows.drop 48) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
