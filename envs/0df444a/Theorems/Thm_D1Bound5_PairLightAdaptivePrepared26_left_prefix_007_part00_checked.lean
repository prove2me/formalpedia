-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_007_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_007_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:20:00.202721+00:00
-- url     : https://prove2.me/theorems/6e3a8c74-be7f-4684-a91a-0608531aa37c
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 0
-- statement:
--   For prepared pair 26, left list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 616 through 627; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_007Part00.lean, lines 7-11, SHA-256 2563a90bfdd6efe5b7b44db25af6e82389c467dd11e678fa8a0ff9eb9c6a598b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_007_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached007.drop 0) (leftRows007.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
