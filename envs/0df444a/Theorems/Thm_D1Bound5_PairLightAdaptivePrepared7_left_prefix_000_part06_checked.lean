-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_000_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.left_prefix_000_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:21.07382+00:00
-- url     : https://prove2.me/theorems/a65540b9-8cb0-485a-af55-3dfb28540ccb
-- title:
--   Selected-floor prefix certificate for prepared pair 7, left list, part 6
-- statement:
--   For prepared pair 7, left list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 72 through 83, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft7_000Part06.lean, lines 11-16, SHA-256 15c8751f02fafee6046e04f169e9f093e432ba2504346978b6c8da295647efde. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.left_prefix_000_part06_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 12
      (PairLightPrepared7.leftCached.drop 72)
      (PairLightPrepared7.leftRows.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
