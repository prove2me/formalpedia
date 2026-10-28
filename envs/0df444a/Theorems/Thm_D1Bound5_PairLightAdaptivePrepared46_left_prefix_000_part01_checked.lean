-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_left_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.left_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:33.425667+00:00
-- url     : https://prove2.me/theorems/6242ce92-86cb-4c44-b6f3-df11982c3a60
-- title:
--   Selected-floor prefix certificate for prepared pair 46, left list, part 1
-- statement:
--   For prepared pair 46, left list, part 1, the selected-floor certificate succeeds for at most `20` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Original heads 16 through 35, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft46_000Part01.lean, lines 7-11, SHA-256 2a933b2b9515ad79c0724ba0ecf0c0b5ddc132cc45e978471e85927e35a74f41. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.left_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 20
      (leftCached000.drop 16) (leftRows000.drop 16) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
