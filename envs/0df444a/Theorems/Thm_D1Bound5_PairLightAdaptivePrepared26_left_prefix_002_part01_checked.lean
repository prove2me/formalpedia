-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_002_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:34.16599+00:00
-- url     : https://prove2.me/theorems/babe47d2-64c0-4421-9117-bde260b289db
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 1
-- statement:
--   For prepared pair 26, left list, part 1, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 116 through 118; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_002Part01.lean, lines 7-11, SHA-256 1c1358f2d3eefc4493ae032fc0e00c181e21c413f384bac6299562e2f91c95f9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached002.drop 3) (leftRows002.drop 3) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
