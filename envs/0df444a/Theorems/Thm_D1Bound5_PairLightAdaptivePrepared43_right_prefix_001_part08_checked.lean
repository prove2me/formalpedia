-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_001_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.right_prefix_001_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:12.79022+00:00
-- url     : https://prove2.me/theorems/e3e8dbee-1ecc-4372-b61c-535ae9e90b63
-- title:
--   Selected-floor prefix certificate for prepared pair 43, right list, part 8
-- statement:
--   For prepared pair 43, right list, part 8, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 188 through 199, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight43_001Part08.lean, lines 9-14, SHA-256 627a7f6c3124e7f6009d28055590c900a7a2052fc35bd79a37a7297f89242cb2. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.right_prefix_001_part08_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.rightCached.drop 188)
      (PairLightPrepared43.rightRows.drop 188) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
