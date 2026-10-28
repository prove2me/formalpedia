-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.left_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:20.677058+00:00
-- url     : https://prove2.me/theorems/ec01baa8-cbbc-4254-9438-3a1bef32975d
-- title:
--   Selected-floor prefix certificate for prepared pair 3, left list, part 1
-- statement:
--   For prepared pair 3, left list, part 1, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 136 through 159, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft3_001Part01.lean, lines 9-14, SHA-256 0891804ab4aefa4e94bfbae7621c5324adfa4d095d4d981e645f2ff6b9245004. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.left_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 24
      (PairLightPrepared3.leftCached.drop 136)
      (PairLightPrepared3.leftRows.drop 136) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
