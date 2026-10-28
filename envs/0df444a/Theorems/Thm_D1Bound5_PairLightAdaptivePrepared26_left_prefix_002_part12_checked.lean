-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_002_part12_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part12_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:16.068581+00:00
-- url     : https://prove2.me/theorems/88da1156-91b0-4623-a04d-09cd6acee6c9
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 12
-- statement:
--   For prepared pair 26, left list, part 12, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 149 through 151; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_002Part12.lean, lines 7-11, SHA-256 5ffc182d0f28805eb1c4a2debf7bec2c237dbd28fbeefefc91ad394a4fb018fd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part12_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached002.drop 36) (leftRows002.drop 36) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
