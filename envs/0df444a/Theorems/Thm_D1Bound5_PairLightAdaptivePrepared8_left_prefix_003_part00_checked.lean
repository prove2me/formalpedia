-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_003_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_003_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:20:02.07544+00:00
-- url     : https://prove2.me/theorems/2015936c-a9d7-49c7-bff9-bb8eb8004bfd
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 0
-- statement:
--   For prepared pair 8, left list, part 0, the selected-floor certificate succeeds for at most `13` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 192 through 204, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_003Part00.lean, lines 11-16, SHA-256 ebcec13b1258221b5de9506ea043dd2d5f883f7b6591f0dcd5bdddc3a79391c0. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_003_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 13
      (PairLightPrepared8.leftCached.drop 192)
      (PairLightPrepared8.leftRows.drop 192) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
