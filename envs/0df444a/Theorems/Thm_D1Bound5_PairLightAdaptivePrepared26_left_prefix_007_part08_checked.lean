-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_007_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_007_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:54.778272+00:00
-- url     : https://prove2.me/theorems/f7c52c1f-fb48-4513-bf87-6811cf5336dd
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 8
-- statement:
--   For prepared pair 26, left list, part 8, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 712 through 723; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_007Part08.lean, lines 7-11, SHA-256 028493d259b11adcf9903a1c8191d3b8df2c02020f4f8cfa237b515e12aed31a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_007_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached007.drop 96) (leftRows007.drop 96) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
