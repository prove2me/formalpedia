-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.left_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:04.226322+00:00
-- url     : https://prove2.me/theorems/f669f24f-278a-450b-bd1d-f8799066f983
-- title:
--   Selected-floor prefix certificate for prepared pair 43, left list, part 2
-- statement:
--   For prepared pair 43, left list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 24 through 35, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft43_000Part02.lean, lines 8-13, SHA-256 af6df3e66262d8931936073d81c04e8e8ae99b383febba19245676ee1c9b9030. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.left_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.leftCached.drop 24)
      (PairLightPrepared43.leftRows.drop 24) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
