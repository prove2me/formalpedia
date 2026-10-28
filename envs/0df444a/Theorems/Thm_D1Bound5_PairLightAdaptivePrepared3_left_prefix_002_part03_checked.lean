-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_002_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.left_prefix_002_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:01.542521+00:00
-- url     : https://prove2.me/theorems/a7a82cb7-b6a0-4bba-bf94-06047435d6d6
-- title:
--   Selected-floor prefix certificate for prepared pair 3, left list, part 3
-- statement:
--   For prepared pair 3, left list, part 3, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 383 through 406, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft3_002Part03.lean, lines 9-14, SHA-256 d267401f5ea52c4cd3baa9c3cd61b24dba478fe276986daf83e60e67c999cddd. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.left_prefix_002_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 24
      (PairLightPrepared3.leftCached.drop 383)
      (PairLightPrepared3.leftRows.drop 383) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
