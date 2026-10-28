-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared1.left_prefix_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:21:35.716563+00:00
-- url     : https://prove2.me/theorems/13c3ab6b-d04a-4032-a948-b76d68b24882
-- title:
--   Selected-floor prefix certificate for prepared pair 1, left list, part 5
-- statement:
--   For prepared pair 1, left list, part 5, the selected-floor certificate succeeds for at most `29` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared1.sieve`. Original heads 108 through 136, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft1_000Part05.lean, lines 7-11, SHA-256 0308b73aa3d59a645676bd4b9c5228a93b9bb644d62538f5da0aca40d7480b17. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared1.left_prefix_000_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 29
      (leftCached000.drop 108) (leftRows000.drop 108) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared1
end
