-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared33_left_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared33.left_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:55:12.050076+00:00
-- url     : https://prove2.me/theorems/101f3b3b-c789-4287-bccd-0d5f901ddd59
-- title:
--   Selected-floor prefix certificate for prepared pair 33, left list, part 1
-- statement:
--   For prepared pair 33, left list, part 1, the selected-floor certificate succeeds for at most `31` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared33.sieve`. Original heads 28 through 58; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft33_000Part01.lean, lines 7-11, SHA-256 8d0e05aa72badbd3ce5cbd48b4d3d24a0cde6bbd37ec618cda4faf872ca51d20. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData33_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared33.left_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared33.sieve 31
      (leftCached000.drop 28) (leftRows000.drop 28) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared33
end
