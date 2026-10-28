-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part10_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_006_part10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:22.645979+00:00
-- url     : https://prove2.me/theorems/388c8d96-0377-4965-accc-84ba66a11bb6
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 10
-- statement:
--   For prepared pair 26, right list, part 10, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 563 through 574; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_006Part10.lean, lines 7-11, SHA-256 63bd117af8bd655fc7a155f6abe60b9013a8d826f8f81f59aecfefb3066b5be4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_006_part10_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached006.drop 120) (rightRows006.drop 120) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
