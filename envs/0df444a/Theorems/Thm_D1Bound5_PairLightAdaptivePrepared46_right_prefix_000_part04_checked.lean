-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_right_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared46.right_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:02:14.213961+00:00
-- url     : https://prove2.me/theorems/a8065b62-e56c-4381-a932-0b8160a0e1ab
-- title:
--   Selected-floor prefix certificate for prepared pair 46, right list, part 4
-- statement:
--   For prepared pair 46, right list, part 4, the selected-floor certificate succeeds for at most `26` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 6, and the sieve is `PairLightPrepared46.sieve`. Original heads 82 through 107, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight46_000Part04.lean, lines 7-11, SHA-256 ffd81fd1c6283471e43116a9b37be4a6260bf8bc0c7620392c353c5e1b928442. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared46.right_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 26
      (rightCached000.drop 82) (rightRows000.drop 82) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared46
end
