-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_left_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared40.left_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:05.19915+00:00
-- url     : https://prove2.me/theorems/84cf4be6-957e-4f03-a8e0-87a85b9a5bf3
-- title:
--   Selected-floor prefix certificate for prepared pair 40, left list, part 1
-- statement:
--   For prepared pair 40, left list, part 1, the selected-floor certificate succeeds for at most `73` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared40.sieve`. Original heads 187 through 259; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft40_001Part01.lean, lines 7-11, SHA-256 d07e9ff4f43ede774a796599cba069aa157ed6658e15a673355101ad86a252a1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared40.left_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 73
      (leftCached001.drop 50) (leftRows001.drop 50) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared40
end
