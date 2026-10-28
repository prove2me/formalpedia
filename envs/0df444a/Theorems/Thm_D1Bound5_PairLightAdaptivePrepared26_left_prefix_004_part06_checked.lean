-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_004_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_004_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:09.667894+00:00
-- url     : https://prove2.me/theorems/55d882b5-fda2-4c44-ad7a-fb07d840cdb8
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 6
-- statement:
--   For prepared pair 26, left list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 323 through 334; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_004Part06.lean, lines 7-11, SHA-256 834eb39ca61ad958f0f42d99917c4ffe76f700bcff6ba13d2d567bfc1fcc7cc5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_004_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached004.drop 72) (leftRows004.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
