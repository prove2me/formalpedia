-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_005_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.left_prefix_005_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:33:18.612979+00:00
-- url     : https://prove2.me/theorems/b253062b-57b3-483e-9470-7e2b2b906d01
-- title:
--   Selected-floor prefix certificate for prepared pair 8, left list, part 5
-- statement:
--   For prepared pair 8, left list, part 5, the selected-floor certificate succeeds for at most `31` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`. Original heads 493 through 523, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft8_005Part05.lean, lines 11-16, SHA-256 6ba4fe8e2af1a666682d16a12a11f9b1e954684ef05f3a7f78d60ec0a7c8bdaf. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared8.left_prefix_005_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 31
      (PairLightPrepared8.leftCached.drop 493)
      (PairLightPrepared8.leftRows.drop 493) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
