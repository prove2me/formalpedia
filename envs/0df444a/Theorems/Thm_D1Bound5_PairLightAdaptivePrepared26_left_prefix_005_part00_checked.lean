-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_005_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_005_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:00.69499+00:00
-- url     : https://prove2.me/theorems/d7ac71bd-e89a-4d66-bc42-a5c0a29e6411
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 0
-- statement:
--   For prepared pair 26, left list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 336 through 347; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_005Part00.lean, lines 7-11, SHA-256 75a76fb458d848360a1caaebfe491c0036439c8f16452b64974710acd1557d65. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_005_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached005.drop 0) (leftRows005.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
