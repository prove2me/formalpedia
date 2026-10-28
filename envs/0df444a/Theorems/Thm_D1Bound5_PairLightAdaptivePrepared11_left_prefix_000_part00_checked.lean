-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_left_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared11.left_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:37.745334+00:00
-- url     : https://prove2.me/theorems/f1764096-6709-43ca-ad36-3d75f38ee79b
-- title:
--   Selected-floor prefix certificate for prepared pair 11, left list, part 0
-- statement:
--   For prepared pair 11, left list, part 0, the selected-floor certificate succeeds for at most `16` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared11.sieve`. Original heads 0 through 15, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft11_000Part00.lean, lines 7-11, SHA-256 257b7053a7a0d46287f71695527a68c94d136150f4601ba810d06515f60bd432. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared11.left_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 16
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared11
end
