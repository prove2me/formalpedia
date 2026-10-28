-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part13_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_006_part13_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:12.04364+00:00
-- url     : https://prove2.me/theorems/01f9cf1a-5b6e-43c6-81b8-e6176cbd3d6a
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 13
-- statement:
--   For prepared pair 26, right list, part 13, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 599 through 610; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_006Part13.lean, lines 7-11, SHA-256 4182c805fb2047abfcffb8a71ffec20389a2f34fda06572a791fb16f602849b5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_006_part13_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached006.drop 156) (rightRows006.drop 156) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
