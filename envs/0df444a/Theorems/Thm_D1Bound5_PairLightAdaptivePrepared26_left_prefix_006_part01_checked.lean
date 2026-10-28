-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_006_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_006_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:28.087559+00:00
-- url     : https://prove2.me/theorems/088c9973-4a13-4bac-975d-7bf52b6d7a70
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 1
-- statement:
--   For prepared pair 26, left list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 455 through 466; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_006Part01.lean, lines 7-11, SHA-256 893cc8bdbea848919aedf4b74fc69f06836d07e14178cf7d0af8c3fc6d00d169. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_006_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached006.drop 12) (leftRows006.drop 12) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
