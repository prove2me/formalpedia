-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.left_prefix_002_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:41.182187+00:00
-- url     : https://prove2.me/theorems/83a881cd-09ad-4376-9e8e-8f720851ddf8
-- title:
--   Selected-floor prefix certificate for prepared pair 43, left list, part 2
-- statement:
--   For prepared pair 43, left list, part 2, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 260 through 283, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft43_002Part02.lean, lines 8-13, SHA-256 dce3f4bd4c872fcba157efa42d0d110d338a1074a486a7dc9649c05cb97d25d9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.left_prefix_002_part02_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 24
      (PairLightPrepared43.leftCached.drop 260)
      (PairLightPrepared43.leftRows.drop 260) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
