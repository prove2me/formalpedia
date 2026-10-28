-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_001_part10_checked
-- name    : D1Bound5.PairLightAdaptivePrepared43.left_prefix_001_part10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:00.857783+00:00
-- url     : https://prove2.me/theorems/ea5a4843-c0d8-4e4e-adc3-ff434ec16735
-- title:
--   Selected-floor prefix certificate for prepared pair 43, left list, part 10
-- statement:
--   For prepared pair 43, left list, part 10, the selected-floor certificate succeeds for at most `1` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 3, and the sieve is `PairLightPrepared43.sieve`. Original heads 211 through 211, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft43_001Part10.lean, lines 8-13, SHA-256 24578f0f551b324a706a1a9ce201ab380bfc54ca23608904c1387d7c9793869a. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared43.left_prefix_001_part10_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 1
      (PairLightPrepared43.leftCached.drop 211)
      (PairLightPrepared43.leftRows.drop 211) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared43
end
