-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_002_part18_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part18_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:58.721001+00:00
-- url     : https://prove2.me/theorems/78931d47-b965-4989-a7cc-1c946d1f675c
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 18
-- statement:
--   For prepared pair 26, left list, part 18, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 167 through 169; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_002Part18.lean, lines 7-11, SHA-256 aa4ffa78442f50c18f738c9bf58aa538e366de76c2c58074eb649e394a9e8a3d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part18_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached002.drop 54) (leftRows002.drop 54) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
