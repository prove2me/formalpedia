-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_001_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.right_prefix_001_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:58.268984+00:00
-- url     : https://prove2.me/theorems/fee854d4-2e84-4a0e-b0a1-b5d063e81c6d
-- title:
--   Selected-floor prefix certificate for prepared pair 3, right list, part 8
-- statement:
--   For prepared pair 3, right list, part 8, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 303 through 305, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight3_001Part08.lean, lines 10-15, SHA-256 a08841ba9b4a2970d1c08b1fd6cc16cb8524df8c62042dc41eaec20a47c99b92. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.right_prefix_001_part08_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 3
      (PairLightPrepared3.rightCached.drop 303)
      (PairLightPrepared3.rightRows.drop 303) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
