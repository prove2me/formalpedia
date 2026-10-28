-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_001_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.left_prefix_001_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:32.927273+00:00
-- url     : https://prove2.me/theorems/67c5bccf-c709-4ffd-92c1-f951c112734e
-- title:
--   Selected-floor prefix certificate for prepared pair 43, left list, part 8
-- statement:
--   For prepared pair 43, left list, part 8, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 187 through 198, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft43_001Part08.lean, lines 8-13, SHA-256 5d2412664776bfa8cd156623faf060d186f835834c7b220535606e063cbb9fbf. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.left_prefix_001_part08_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.leftCached.drop 187)
      (PairLightPrepared43.leftRows.drop 187) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
