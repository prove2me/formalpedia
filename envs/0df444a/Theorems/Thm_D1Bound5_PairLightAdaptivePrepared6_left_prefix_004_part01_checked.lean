-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_004_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_004_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:16.515089+00:00
-- url     : https://prove2.me/theorems/e5ca54dc-5976-4db7-b5a7-2d7335fe24f6
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 1
-- statement:
--   For prepared pair 6, left list, part 1, the selected-floor certificate succeeds for at most `21` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 338 through 358, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_004Part01.lean, lines 11-16, SHA-256 d673b218ab0115f1a365a8dd479a569ba4136d322022e233d134fb8d1915e20b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_004_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 21
      (PairLightPrepared6.leftCached.drop 338)
      (PairLightPrepared6.leftRows.drop 338) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
