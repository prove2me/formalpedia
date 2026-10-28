-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.right_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:02:15.881105+00:00
-- url     : https://prove2.me/theorems/3c652eca-ade1-432b-8fb5-810c3a79c8fc
-- title:
--   Selected-floor prefix certificate for prepared pair 3, right list, part 2
-- statement:
--   For prepared pair 3, right list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 24 through 35, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight3_000Part02.lean, lines 10-15, SHA-256 fc35274cb5a9e5f0a201525b8efd8d8f8401b2dcacb44e92543f72ab67a4c4a1. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.right_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 12
      (PairLightPrepared3.rightCached.drop 24)
      (PairLightPrepared3.rightRows.drop 24) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
