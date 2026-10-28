-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_left_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared40.left_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:21:39.885992+00:00
-- url     : https://prove2.me/theorems/a40085a1-759d-4028-acf4-6a6c498ebcc2
-- title:
--   Selected-floor prefix certificate for prepared pair 40, left list, part 2
-- statement:
--   For prepared pair 40, left list, part 2, the selected-floor certificate succeeds for at most `35` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared40.sieve`. Original heads 59 through 93; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft40_000Part02.lean, lines 7-11, SHA-256 352b89e23f22884ec1bcb9671273768942ab565818ab6a6769925ddce5c21573. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared40.left_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 35
      (leftCached000.drop 59) (leftRows000.drop 59) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared40
end
