-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.left_prefix_002_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:58.779705+00:00
-- url     : https://prove2.me/theorems/a0f45132-5190-4534-a82c-957991fbea86
-- title:
--   Selected-floor prefix certificate for prepared pair 43, left list, part 6
-- statement:
--   For prepared pair 43, left list, part 6, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 356 through 379, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft43_002Part06.lean, lines 8-13, SHA-256 70e3c9dba233aa5abc0fc6428ca2db66c5c89d666a24257813ba60c0475d8804. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.left_prefix_002_part06_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 24
      (PairLightPrepared43.leftCached.drop 356)
      (PairLightPrepared43.leftRows.drop 356) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
